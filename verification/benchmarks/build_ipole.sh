set -eu
# Legacy filename retained for existing callers; the reference is entirely Zig.
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
reference_root="$project_root/target/eht-reference"
# WSL's Windows-mounted filesystem can reject Zig test-cache directory renames.
reference_cache="${TMPDIR:-/tmp}/black-hole-zig-reference"
mkdir -p "$reference_root"
cd "$project_root"
"${ZIG:-zig}" test verification/benchmarks/reference.zig \
    --cache-dir "$reference_cache/local" --global-cache-dir "$reference_cache/global"
"${ZIG:-zig}" build-exe verification/benchmarks/reference.zig -O safe \
    -femit-bin="$reference_root/reference-zig" \
    --cache-dir "$reference_cache/local" --global-cache-dir "$reference_cache/global"
printf 'Standalone Zig reference built (no external libraries).\n'
