set -eu
probe_mode="${1:-snapshot}"
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
reference_root="$project_root/target/eht-reference"
cd "$project_root"
test -x "$reference_root/reference-zig" || {
    printf 'Run verification/benchmarks/build_ipole.sh with Zig 0.17 first.\n' >&2
    exit 1
}
if [ "$probe_mode" = outer ]; then
    "$reference_root/reference-zig" outer verification/benchmarks/eht-ipole.par \
        target/eht-benchmark/outer-ipole.f64 > "$reference_root/outer.log" 2>&1
    exit
fi
if [ "$probe_mode" = camera ]; then
    "$reference_root/reference-zig" camera verification/benchmarks/eht-ipole.par \
        target/eht-benchmark/camera-ipole.f64 > "$reference_root/camera.log" 2>&1
    exit
fi
if [ "$probe_mode" = thermal ]; then
    "$reference_root/reference-zig" thermal target/eht-benchmark/thermal-queries.f64 \
        target/eht-benchmark/thermal-ipole.f64 target/eht-benchmark/thermal-bessel.f32
    exit
fi
if [ "$probe_mode" != snapshot ]; then
    printf 'usage: sample_ipole.sh [snapshot|thermal|camera|outer]\n' >&2
    exit 2
fi
"$reference_root/reference-zig" snapshot verification/benchmarks/eht-ipole.par \
    target/eht-benchmark/sample-queries.f64 target/eht-benchmark/sample-ipole.f64 \
    > "$reference_root/sample.log" 2>&1
