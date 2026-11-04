set -eu
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
reference_root="$project_root/target/eht-reference"
export LD_LIBRARY_PATH="$reference_root/sysroot/usr/lib/x86_64-linux-gnu${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export OMP_NUM_THREADS=4
cd "$project_root"
case "${1:-baseline}" in
    baseline) parameter_file=verification/benchmarks/eht-ipole.par; output_file=target/eht-benchmark/ipole-reference.h5; log_file="$reference_root/run.log" ;;
    refined) parameter_file=verification/benchmarks/eht-ipole-refined.par; output_file=target/eht-benchmark/ipole-reference-refined.h5; log_file="$reference_root/run-refined.log" ;;
    *) printf 'usage: run_ipole.sh [baseline|refined]\n' >&2; exit 2 ;;
esac
"$reference_root/ipole/ipole" -par "$parameter_file" > "$log_file" 2>&1 || {
    tail -50 "$log_file"
    exit 1
}
test -s "$output_file"
tail -25 "$log_file"
