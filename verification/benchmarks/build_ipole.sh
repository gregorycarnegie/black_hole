set -eu
# shortcut: Ubuntu 26.04 amd64 package pins; update pins for another release.
# Dependencies are unpacked locally, without sudo.
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
reference_root="$project_root/target/eht-reference"
mkdir -p "$reference_root/packages" "$reference_root/sysroot"
cd "$reference_root/packages"
apt download libgsl-dev=2.8+dfsg-6 libgsl28=2.8+dfsg-6 libgslcblas0=2.8+dfsg-6 \
    libhdf5-dev=1.14.6+repack-2 libhdf5-310=1.14.6+repack-2 libhdf5-hl-310=1.14.6+repack-2 \
    libsz2=1.1.5-1 libaec0=1.1.5-1
cd "$reference_root/packages"
for reference_package in ./*.deb; do
    dpkg-deb -x "$reference_package" "$reference_root/sysroot"
done
cd "$reference_root"
if [ ! -d ipole/.git ]; then
    git clone --no-checkout https://github.com/AFD-Illinois/ipole.git ipole
fi
git -C ipole checkout --detach 7f7a482cf91125aeeeb9c431485bba680e8941d7
cd ipole
test "$(git rev-parse HEAD)" = 7f7a482cf91125aeeeb9c431485bba680e8941d7
case "$(pwd -P)" in
    "$project_root"/target/eht-reference/ipole) ;;
    *) exit 1 ;;
esac
reference_lib="$reference_root/sysroot/usr/lib/x86_64-linux-gnu"
make -j 4 CC=gcc MODEL=iharm     CFLAGS="-std=gnu99 -O2 -fopenmp"     INC="-Ibuild_archive -I$reference_root/sysroot/usr/include -I$reference_root/sysroot/usr/include/hdf5/serial"     LIBDIR="-L$reference_lib -L$reference_lib/hdf5/serial -Wl,-rpath,$reference_lib"     LIB="-lm -lgsl -lgslcblas -lhdf5_hl -lhdf5" > "$reference_root/build.log" 2>&1 || {
    tail -40 "$reference_root/build.log"
    exit 1
}
test -x ipole
printf 'Independent ipole solver built at pinned commit.\n'
