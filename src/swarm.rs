//! A swarm of small bodies on prescribed circular orbits: a stress test for
//! space-time acceleration structures. The renderer places each body where it
//! was when the light reaching the camera passed it, so inner bodies move
//! several gravitational radii during one photon's crossing of the belt.

use std::f64::consts::TAU;

use bevy::{
    prelude::*,
    render::extract_resource::ExtractResource,
    tasks::{ComputeTaskPool, TaskPool},
};

use crate::camera::OrbitalCamera;

/// Body counts the K key and the panel cycle through.
pub(crate) const SWARM_COUNTS: [u32; 4] = [0, 256, 1024, 4096];
/// Coordinate time, in r_g/c, per real second.
const TIME_SCALE: f64 = 20.0;
/// Outside every Kerr ISCO (at most 9 r_g), so early capture stays valid, and
/// inside the 64 r_g far-field vacuum sphere.
const ORBIT_MIN: f32 = 12.0;
const ORBIT_MAX: f32 = 40.0;
const MAX_INCLINATION: f32 = 0.3;
const MAX_BODY_RADIUS: f32 = 0.5;

#[derive(Resource, Clone, Default, ExtractResource)]
#[extract_app(bevy::render::RenderApp)]
pub(crate) struct Swarm {
    pub count: u32,
    /// Coordinate time at the camera, in r_g/c.
    pub time: f64,
    /// Trace the swarm with RT cores (OptiX) instead of the software BVH. Only
    /// builds with `--features optix` act on it.
    pub rtx: bool,
}

impl Swarm {
    pub(crate) fn step(&mut self, forward: bool) {
        let index = SWARM_COUNTS
            .iter()
            .position(|&count| count == self.count)
            .unwrap_or(0);
        let n = SWARM_COUNTS.len();
        self.count = SWARM_COUNTS[if forward {
            (index + 1) % n
        } else {
            (index + n - 1) % n
        }];
    }
}

/// Matches `SwarmBody` in `tools/cuda/kernels.rs`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
pub(crate) struct GpuSwarmBody {
    /// Orbital axis at phase 0, then orbit radius.
    pub axis_a: [f32; 4],
    /// Direction of motion at phase 0, then body radius.
    pub axis_b: [f32; 4],
    /// Phase at the camera time, angular velocity, albedo, unused.
    pub orbit: [f32; 4],
}

impl GpuSwarmBody {
    /// Centre at camera-relative coordinate time `t`.
    pub(crate) fn center(&self, t: f64) -> [f64; 3] {
        let angle = f64::from(self.orbit[0]) + f64::from(self.orbit[1]) * t;
        let (sin, cos) = angle.sin_cos();
        let r = f64::from(self.axis_a[3]);
        std::array::from_fn(|k| {
            r * (cos * f64::from(self.axis_a[k]) + sin * f64::from(self.axis_b[k]))
        })
    }

    /// A box holding the body, padded as the kernel pads it, while `early ≤ t ≤ late`.
    fn swept_box(&self, early: f64, late: f64) -> [[f32; 3]; 2] {
        let r = f64::from(self.axis_a[3]);
        let turn = f64::from(self.orbit[1]) * (late - early);
        assert!(
            turn.abs() < std::f64::consts::PI,
            "slice too long for the chord bound"
        );
        // The arc stays within its sagitta of the chord; the kernel's per-step
        // padding is at most r turn² / 8; the rest covers binary32 positions.
        let pad = f64::from(self.axis_b[3])
            + r * (1.0 - (0.5 * turn).cos())
            + 0.125 * r * turn * turn
            + 0.01;
        let (a, b) = (self.center(early), self.center(late));
        [
            std::array::from_fn(|k| (a[k].min(b[k]) - pad) as f32),
            std::array::from_fn(|k| (a[k].max(b[k]) + pad) as f32),
        ]
    }
}

/// Width and step limit of the BVH time slices, in r_g/c of camera-relative time.
/// Must match `SWARM_SLICE_WIDTH` and `SWARM_STEP_SPAN` in `tools/cuda/kernels.rs`.
const SLICE_WIDTH: f64 = 8.0;
const STEP_SPAN: f64 = 12.0;
/// Rays older than SLICES × SLICE_WIDTH fall back to brute force.
pub(crate) const SLICES: u32 = 40;
const LEAF_SIZE: usize = 4;
/// Slice trees are cached on a grid of absolute coordinate time with spacing
/// SLICE_WIDTH / TREES_PER_SLICE: tree m covers [m GRID - TREE_SPAN, m GRID], which
/// holds every slice window ending in (m GRID - GRID, m GRID], so a tree serves
/// frames until it ages out. Wider trees cull worse on the GPU: a grid of 8 cost
/// ~1 ms at 4096 bodies, 2 was within noise of exact windows.
const TREES_PER_SLICE: u32 = 4;
const GRID: f64 = SLICE_WIDTH / TREES_PER_SLICE as f64;
const TREE_SPAN: f64 = SLICE_WIDTH + STEP_SPAN + GRID;
/// Slice k uses tree `newest - k TREES_PER_SLICE`, so this many trees are live.
pub(crate) const TREE_SLOTS: usize = ((SLICES - 1) * TREES_PER_SLICE + 1) as usize;

/// One slice's bounding-volume hierarchy in the kernel's layout: node i is
/// `nodes[2i]` (minimum, then the right child or first item as bits) and
/// `nodes[2i + 1]` (maximum, then 0 or the leaf's item count as bits).
#[derive(Default)]
pub(crate) struct SwarmBvh {
    pub nodes: Vec<[f32; 4]>,
    pub items: Vec<u32>,
}

/// Slice trees cached by absolute time, tree m in slot m mod TREE_SLOTS of the
/// device buffers, so a frame builds and uploads only the trees new to it.
#[derive(Default)]
pub(crate) struct SwarmTrees {
    /// Body count and spin bits the held trees were built for.
    key: Option<(u32, u32)>,
    /// Tree index held in each slot.
    held: Vec<Option<i64>>,
    /// Nodes per tree: the median split makes it depend only on the body count.
    pub nodes_per_tree: usize,
}

impl SwarmTrees {
    /// Readies the trees for camera time `time`. Returns each slice's root and the
    /// newly built trees with their slots, linked for those slots.
    pub(crate) fn update(
        &mut self,
        count: u32,
        spin: f32,
        time: f64,
    ) -> (Vec<u32>, Vec<(usize, SwarmBvh)>) {
        let key = Some((count, spin.to_bits()));
        if self.key != key {
            *self = Self {
                key,
                held: vec![None; TREE_SLOTS],
                nodes_per_tree: 0,
            };
        }
        // Integer offsets from one rounding keep the live trees in distinct slots.
        let newest = ((time + 0.5 * STEP_SPAN) / GRID).ceil() as i64;
        let wanted: Vec<i64> = (0..SLICES)
            .map(|k| newest - i64::from(k * TREES_PER_SLICE))
            .collect();
        let slot = |m: i64| m.rem_euclid(TREE_SLOTS as i64) as usize;
        let missing: Vec<i64> = wanted
            .iter()
            .copied()
            .filter(|&m| self.held[slot(m)] != Some(m))
            .collect();
        let pool = ComputeTaskPool::get_or_init(TaskPool::default);
        let built = pool.scope(|scope| {
            for &m in &missing {
                scope.spawn(async move { slice_tree(count, spin, m) });
            }
        });
        let mut fresh = Vec::with_capacity(missing.len());
        for (m, mut tree) in missing.into_iter().zip(built) {
            self.nodes_per_tree = tree.nodes.len() / 2;
            let s = slot(m);
            self.held[s] = Some(m);
            // A non-zero count marks a leaf, whose link is its first item.
            let (node_base, item_base) = ((s * self.nodes_per_tree) as u32, s as u32 * count);
            for [lo, hi] in tree.nodes.as_chunks_mut::<2>().0 {
                let base = if hi[3].to_bits() == 0 {
                    node_base
                } else {
                    item_base
                };
                lo[3] = f32::from_bits(lo[3].to_bits() + base);
            }
            fresh.push((s, tree));
        }
        let roots = wanted
            .iter()
            .map(|&m| (slot(m) * self.nodes_per_tree) as u32)
            .collect();
        (roots, fresh)
    }
}

/// Tree `m`, with links local to it.
fn slice_tree(count: u32, spin: f32, m: i64) -> SwarmBvh {
    let bodies = swarm_bodies(count, spin, m as f64 * GRID);
    let boxes: Vec<_> = bodies
        .iter()
        .map(|b| b.swept_box(-TREE_SPAN, 0.0))
        .collect();
    let mut items: Vec<u32> = (0..count).collect();
    let mut tree = SwarmBvh::default();
    build_node(&mut tree, &boxes, &mut items);
    tree
}

/// (inner, outer, spread) for `beyond_belt` in `tools/cuda/kernels.rs`: every body
/// stays within radii [inner - spread dt^2, outer + spread dt^2] over a step of
/// duration dt, including the sagitta padding of the per-body test. The margins
/// cover rounding.
pub(crate) fn swarm_belt(bodies: &[GpuSwarmBody]) -> (f32, f32, f32) {
    let (mut inner, mut outer, mut spread) = (f32::INFINITY, 0.0_f32, 0.0_f32);
    for body in bodies {
        let (orbit, radius, omega) = (body.axis_a[3], body.axis_b[3], body.orbit[1]);
        inner = inner.min(orbit - radius - 0.01);
        outer = outer.max(orbit + radius + 0.01);
        spread = spread.max(0.125 * orbit * omega * omega * 1.001);
    }
    (inner, outer, spread)
}

fn build_node(bvh: &mut SwarmBvh, boxes: &[[[f32; 3]; 2]], items: &mut [u32]) -> u32 {
    let node = (bvh.nodes.len() / 2) as u32;
    let mut lo = [f32::INFINITY; 3];
    let mut hi = [f32::NEG_INFINITY; 3];
    for &item in items.iter() {
        for k in 0..3 {
            lo[k] = lo[k].min(boxes[item as usize][0][k]);
            hi[k] = hi[k].max(boxes[item as usize][1][k]);
        }
    }
    bvh.nodes.push([lo[0], lo[1], lo[2], 0.0]);
    bvh.nodes.push([hi[0], hi[1], hi[2], 0.0]);
    let (link, count) = if items.len() <= LEAF_SIZE {
        let first = bvh.items.len() as u32;
        bvh.items.extend_from_slice(items);
        (first, items.len() as u32)
    } else {
        // Median split of the box centres along the widest axis.
        let axis = (0..3)
            .max_by(|&a, &b| (hi[a] - lo[a]).total_cmp(&(hi[b] - lo[b])))
            .unwrap();
        let centre = |item: &u32| boxes[*item as usize][0][axis] + boxes[*item as usize][1][axis];
        let middle = items.len() / 2;
        items.select_nth_unstable_by(middle, |a, b| centre(a).total_cmp(&centre(b)));
        let (left, right) = items.split_at_mut(middle);
        build_node(bvh, boxes, left); // The left child follows its parent.
        (build_node(bvh, boxes, right), 0)
    };
    bvh.nodes[2 * node as usize][3] = f32::from_bits(link);
    bvh.nodes[2 * node as usize + 1][3] = f32::from_bits(count);
    node
}

pub struct SwarmPlugin;

impl Plugin for SwarmPlugin {
    fn build(&self, app: &mut App) {
        app.insert_resource(Swarm {
            rtx: std::env::args_os().any(|arg| arg == "--optix"),
            ..default()
        })
        .add_systems(Update, (cycle_swarm, advance_swarm).chain());
    }
}

fn cycle_swarm(keys: Res<ButtonInput<KeyCode>>, mut swarm: ResMut<Swarm>) {
    if keys.just_pressed(KeyCode::KeyK) {
        swarm.step(true);
        info!("Swarm bodies: {}", swarm.count);
    }
}

fn advance_swarm(time: Res<Time>, mut swarm: ResMut<Swarm>, mut cam: ResMut<OrbitalCamera>) {
    if swarm.count > 0 {
        swarm.time += time.delta_secs_f64() * TIME_SCALE;
        // The scene changes every frame, so temporal accumulation must restart.
        cam.is_moving = true;
    }
}

/// Deterministic uniform numbers in [0, 1) for body `index`.
fn unit_randoms<const N: usize>(index: u32) -> [f32; N] {
    std::array::from_fn(|k| {
        // splitmix64
        let mut z = (u64::from(index) << 8 | k as u64).wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        ((z ^ (z >> 31)) >> 40) as f32 / (1u64 << 24) as f32
    })
}

/// Bodies on a thick belt, prograde about +y, with phases at camera time `time`.
// shortcut: inclined orbits use the Kerr equatorial frequency and are not geodesics; switch to Kerr circular-orbit data if the physics matters.
pub(crate) fn swarm_bodies(count: u32, spin: f32, time: f64) -> Vec<GpuSwarmBody> {
    (0..count)
        .map(|index| {
            let [u_radius, u_node, u_tilt, u_phase, u_size, u_albedo] = unit_randoms(index);
            // Uniform per unit area across the belt.
            let r = (ORBIT_MIN * ORBIT_MIN
                + u_radius * (ORBIT_MAX * ORBIT_MAX - ORBIT_MIN * ORBIT_MIN))
                .sqrt();
            let node = std::f32::consts::TAU * u_node;
            let tilt = MAX_INCLINATION * (2.0 * u_tilt - 1.0);
            let (node_sin, node_cos) = node.sin_cos();
            let axis_a = Vec3::new(node_cos, 0.0, -node_sin);
            // Matches the disk's rotation sense, tangent (z, 0, -x).
            let axis_b = Vec3::new(-node_sin, 0.0, -node_cos) * tilt.cos() + Vec3::Y * tilt.sin();
            let omega = 1.0 / (f64::from(r).powf(1.5) + f64::from(spin));
            let phase = (TAU * f64::from(u_phase) + omega * time).rem_euclid(TAU);
            GpuSwarmBody {
                axis_a: axis_a.extend(r).into(),
                axis_b: axis_b
                    .extend(0.15 + (MAX_BODY_RADIUS - 0.15) * u_size * u_size)
                    .into(),
                orbit: [phase as f32, omega as f32, 0.35 + 0.65 * u_albedo, 0.0],
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rstest::rstest;

    #[rstest]
    #[case::off_to_first(0, true, 256)]
    #[case::last_wraps_to_off(4096, true, 0)]
    #[case::off_back_to_last(0, false, 4096)]
    #[case::unknown_counts_as_off(7, true, 256)]
    fn counts_cycle_through_the_presets(
        #[case] start: u32,
        #[case] forward: bool,
        #[case] expected: u32,
    ) {
        let mut swarm = Swarm {
            count: start,
            ..Swarm::default()
        };
        swarm.step(forward);
        assert_eq!(swarm.count, expected);
    }

    #[test]
    fn k_cycles_and_an_active_swarm_resets_accumulation() {
        let mut app = App::new();
        app.add_plugins(MinimalPlugins)
            .init_resource::<ButtonInput<KeyCode>>()
            .init_resource::<OrbitalCamera>()
            .add_plugins(SwarmPlugin);
        app.update();
        assert!(!app.world().resource::<OrbitalCamera>().is_moving);
        app.world_mut()
            .resource_mut::<ButtonInput<KeyCode>>()
            .press(KeyCode::KeyK);
        app.update();
        assert_eq!(app.world().resource::<Swarm>().count, 256);
        assert!(app.world().resource::<OrbitalCamera>().is_moving);
    }

    #[rstest]
    #[case::one_leaf(3)]
    #[case::uneven(1000)]
    fn each_slice_root_holds_every_body_once_inside_nested_boxes(#[case] count: u32) {
        // Follow the cache across frames on a host copy of the device buffers.
        let mut trees = SwarmTrees::default();
        let (mut nodes, mut items) = (Vec::new(), Vec::new());
        let mut time = 77.0;
        // Steps shorter and longer than the grid, then a spin change that rebuilds all.
        let steps = [0.3, 1.7, 2.0, 9.0, 0.05].into_iter().cycle().take(60);
        for (frame, dt) in steps.enumerate() {
            let spin = if frame < 50 { 0.82 } else { 0.5 };
            time += dt;
            let (roots, fresh) = trees.update(count, spin, time);
            let (n, c) = (trees.nodes_per_tree, count as usize);
            nodes.resize(2 * n * TREE_SLOTS, [f32::NAN; 4]);
            items.resize(c * TREE_SLOTS, u32::MAX);
            for (slot, tree) in fresh {
                nodes[2 * n * slot..2 * n * (slot + 1)].copy_from_slice(&tree.nodes);
                items[c * slot..c * (slot + 1)].copy_from_slice(&tree.items);
            }
            assert_eq!(roots.len(), SLICES as usize);
            let bodies = swarm_bodies(count, spin, time);
            let contains = |outer: usize, inner: usize| {
                (0..3).all(|k| {
                    nodes[2 * outer][k] <= nodes[2 * inner][k]
                        && nodes[2 * outer + 1][k] >= nodes[2 * inner + 1][k]
                })
            };
            for (slice, &root) in roots.iter().enumerate() {
                let mut seen = vec![0u32; c];
                let mut stack = vec![root as usize];
                while let Some(node) = stack.pop() {
                    let link = nodes[2 * node][3].to_bits() as usize;
                    let leaf = nodes[2 * node + 1][3].to_bits() as usize;
                    if leaf == 0 {
                        assert!(contains(node, node + 1) && contains(node, link));
                        stack.extend([node + 1, link]);
                    } else {
                        assert!(leaf <= LEAF_SIZE);
                        for &item in &items[link..link + leaf] {
                            seen[item as usize] += 1;
                            // This frame's box over the slice's whole window fits the leaf.
                            let late = -(slice as f64) * SLICE_WIDTH + 0.5 * STEP_SPAN;
                            let early = late - SLICE_WIDTH - STEP_SPAN;
                            let b = bodies[item as usize].swept_box(early, late);
                            assert!((0..3).all(|k| nodes[2 * node][k] <= b[0][k]
                                && nodes[2 * node + 1][k] >= b[1][k]));
                        }
                    }
                }
                assert!(seen.iter().all(|&n| n == 1), "frame {frame} slice {slice}");
            }
        }
    }

    #[test]
    fn steady_frames_build_at_most_one_tree() {
        let mut trees = SwarmTrees::default();
        // GRID / 8 per frame: the newest tree index advances every eighth frame.
        let built: Vec<usize> = (0..400)
            .map(|frame| trees.update(16, 0.82, frame as f64 * GRID / 8.0).1.len())
            .collect();
        assert_eq!(built[0], SLICES as usize);
        // Once TREES_PER_SLICE grid steps have filled every slot, one tree enters per step.
        let warm = 8 * TREES_PER_SLICE as usize + 1;
        for (frame, &n) in built.iter().enumerate().skip(warm) {
            // ceil((t + STEP_SPAN / 2) / GRID) = ceil(frame / 8) + 3 steps up on frames 1 mod 8.
            assert_eq!(n, usize::from(frame % 8 == 1), "frame {frame}: {built:?}");
        }
        assert_eq!(trees.update(16, 0.82, 399.0 * GRID / 8.0).1.len(), 0);
    }

    proptest! {
        #[test]
        fn swept_boxes_hold_the_body_throughout_the_window(index in 0u32..256, early in -400.0..0.0_f64, span in 0.0..20.0_f64, s in 0.0..=1.0_f64) {
            let body = swarm_bodies(index + 1, 0.82, 5.0)[index as usize];
            let [lo, hi] = body.swept_box(early, early + span);
            let c = body.center(early + s * span);
            let r = f64::from(body.axis_b[3]);
            prop_assert!((0..3).all(|k| f64::from(lo[k]) <= c[k] - r && c[k] + r <= f64::from(hi[k])));
        }
    }

    #[test]
    fn bodies_are_deterministic() {
        let spin = 0.82;
        assert_eq!(swarm_bodies(64, spin, 3.0), swarm_bodies(64, spin, 3.0));
        assert_ne!(
            swarm_bodies(64, spin, 3.0)[0],
            swarm_bodies(64, spin, 3.0)[1]
        );
    }

    proptest! {
        #[test]
        fn bodies_stay_in_the_belt_on_prograde_orbits(index in 0u32..16384, time in 0.0..1.0e6_f64) {
            let spin = 0.82;
            let body = swarm_bodies(index + 1, spin, time)[index as usize];
            let a = Vec3::from_slice(&body.axis_a);
            let b = Vec3::from_slice(&body.axis_b);
            prop_assert!((a.length() - 1.0).abs() < 1e-5 && (b.length() - 1.0).abs() < 1e-5);
            prop_assert!(a.dot(b).abs() < 1e-5);
            // Angular momentum along +y, within the inclination limit.
            prop_assert!(a.cross(b).y >= MAX_INCLINATION.cos() - 1e-5);
            prop_assert!((ORBIT_MIN..=ORBIT_MAX).contains(&body.axis_a[3]));
            prop_assert!(body.axis_b[3] <= MAX_BODY_RADIUS && body.axis_a[3] - body.axis_b[3] > 9.0);
            prop_assert!((0.0..=std::f32::consts::TAU).contains(&body.orbit[0]));
        }

        #[test]
        fn camera_relative_time_matches_absolute_time(index in 0u32..1024, time in 0.0..1.0e5_f64, dt in -500.0..0.0_f64) {
            let spin = 0.82;
            let now = swarm_bodies(index + 1, spin, time)[index as usize];
            let earlier = swarm_bodies(index + 1, spin, time + dt)[index as usize];
            let [x, y, z] = now.center(dt);
            let [ex, ey, ez] = earlier.center(0.0);
            prop_assert!((x - ex).hypot(y - ey).hypot(z - ez) < 1e-3, "{:?} {:?}", now.center(dt), earlier.center(0.0));
        }
    }
}
