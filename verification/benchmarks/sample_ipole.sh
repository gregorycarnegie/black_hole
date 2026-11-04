set -eu
probe_mode="${1:-snapshot}"
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
reference_root="$project_root/target/eht-reference"
cd "$reference_root/ipole"
test "$(git rev-parse HEAD)" = 7f7a482cf91125aeeeb9c431485bba680e8941d7
test -z "$(git status --porcelain --untracked-files=no)"
reference_lib="$reference_root/sysroot/usr/lib/x86_64-linux-gnu"
# Compile the saved solver sources, replacing only its entry point.
set --
for reference_object in build_archive/*.c; do
    case "$reference_object" in */main.c) ;; *) set -- "$@" "$reference_object" ;; esac
done
gcc -std=gnu99 -O2 -fopenmp -Ibuild_archive -I"$reference_root/sysroot/usr/include" \
    -I"$reference_root/sysroot/usr/include/hdf5/serial" \
    "$project_root/verification/benchmarks/sample_ipole.c" "$@" \
    -L"$reference_lib" -L"$reference_lib/hdf5/serial" \
    -Wl,-rpath,"$reference_lib" -lm -lgsl -lgslcblas -lhdf5_hl -lhdf5 \
    -o "$reference_root/sample-ipole"
export LD_LIBRARY_PATH="$reference_lib:$reference_lib/hdf5/serial${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export OMP_NUM_THREADS=4
cd "$project_root"
if [ "$probe_mode" = outer ]; then
    "$reference_root/sample-ipole" verification/benchmarks/eht-ipole.par --outer \
        target/eht-benchmark/outer-ipole.f64 > "$reference_root/outer.log" 2>&1
    exit
fi
if [ "$probe_mode" = camera ]; then
    "$reference_root/sample-ipole" verification/benchmarks/eht-ipole.par --camera \
        target/eht-benchmark/camera-ipole.f64 > "$reference_root/camera.log" 2>&1
    exit
fi
if [ "$probe_mode" = thermal ]; then
    "$reference_root/sample-ipole" --thermal target/eht-benchmark/thermal-queries.f64 \
        target/eht-benchmark/thermal-ipole.f64 target/eht-benchmark/thermal-bessel.f32
    exit
fi
"$reference_root/sample-ipole" verification/benchmarks/eht-ipole.par \
    target/eht-benchmark/sample-queries.f64 target/eht-benchmark/sample-ipole.f64 \
    > "$reference_root/sample.log" 2>&1
