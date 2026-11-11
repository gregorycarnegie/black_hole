set -eu
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
reference_root="$project_root/target/eht-reference"
cd "$project_root"
case "${1:-baseline}" in
    baseline) parameter_file=verification/benchmarks/eht-ipole.par; output_file=target/eht-benchmark/zig-reference.f64; log_file="$reference_root/run.log" ;;
    refined) parameter_file=verification/benchmarks/eht-ipole-refined.par; output_file=target/eht-benchmark/zig-reference-refined.f64; log_file="$reference_root/run-refined.log" ;;
    *) printf 'usage: run_ipole.sh [baseline|refined]\n' >&2; exit 2 ;;
esac
"$reference_root/reference-zig" image "$parameter_file" "$output_file" > "$log_file" 2>&1 || {
    tail -50 "$log_file"
    exit 1
}
test -s "$output_file"
tail -25 "$log_file"
