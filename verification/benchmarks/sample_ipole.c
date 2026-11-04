/* Query the unmodified pinned iharm implementation, without tracing an image. */
#include "decs.h"
#include "model.h"
#include "coordinates.h"
#include "par.h"
#include <string.h>
#include "thermal_ipole.h"

Params params = {0};
double tf = 0.;
#include "camera_ipole.h"

int main(int argc, char **argv)
{
    if (argc == 5 && strcmp(argv[1], "--thermal") == 0)
        return thermal_probe(argv[2], argv[3], argv[4]);
    if (argc != 4 || sizeof(double) != 8) return 2;
    char *args[] = {argv[0], "-par", argv[1]};
    double tA, tB;
    load_par_from_argv(3, args, &params);
    init_model(&tA, &tB);
    if (strcmp(argv[2], "--camera") == 0) return camera_probe(argv[3]);
    if (strcmp(argv[2], "--outer") == 0) return outer_probe(argv[3]);
    FILE *in = fopen(argv[2], "rb"), *out = fopen(argv[3], "wb");
    if (!in || !out) return 3;
    double X[4] = {4501.677840911209, 0, 0, 0};
    size_t count;
    while ((count = fread(X + 1, sizeof(double), 3, in)) == 3) {
        double row[40], ucov[4], bcov[4], K[4] = {0}, g[4][4];
        get_model_primitives(X, row);
        get_model_fourv(X, K, row + 8, ucov, row + 12, bcov);
        row[16] = get_model_ne(X);
        row[17] = get_model_thetae(X);
        row[18] = get_model_b(X);
        row[19] = get_model_sigma(X);
        gcov_func(X, g);
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < 4; ++j) row[20 + 4*i + j] = g[i][j];
        double r, th, cx, cy, cz;
        bl_coord(X, &r, &th);
        sks_to_cks(r, th, X[3], &cx, &cy, &cz);
        row[36] = cx; row[37] = cz; row[38] = -cy;
        row[39] = radiating_region(X);
        if (fwrite(row, sizeof(double), 40, out) != 40) return 4;
    }
    int failed = count != 0 || ferror(in);
    failed |= fclose(in) != 0;
    failed |= fclose(out) != 0;
    return failed ? 5 : 0;
}
