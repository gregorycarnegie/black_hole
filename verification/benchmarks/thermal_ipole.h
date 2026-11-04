/* Direct queries to the pinned thermal fits, with observer-scaled CGS output. */
#include "fits.h"
#include "radiation.h"
#include <stdint.h>
#include <gsl/gsl_errno.h>
#include <gsl/gsl_sf_bessel.h>

static int thermal_probe(const char *input, const char *output, const char *table)
{
    gsl_set_error_handler_off();
    FILE *in = fopen(input, "rb"), *out = fopen(output, "wb"), *tab = fopen(table, "wb");
    if (!in || !out || !tab) return 3;
    /* Find the first binary32 temperature whose K2 does not underflow in GSL. */
    union { float f; uint32_t bits; } low = {.f = 0.001f}, high = {.f = 0.002f}, mid;
    while (high.bits-low.bits > 1) {
        mid.bits = low.bits+(high.bits-low.bits)/2;
        if (gsl_sf_bessel_Kn(2, 1./mid.f) > 0) high.bits = mid.bits;
        else low.bits = mid.bits;
    }
    double logmin = log(0.002), step = (log(1000)-logmin)/8192.;
    float header[4] = {logmin, step, high.f, 1000};
    if (fwrite(header, sizeof(float), 4, tab) != 4) return 4;
    for (int i=0; i<=8192; ++i) {
        double temperature = exp(logmin+i*step), z = 1./temperature;
        double k2 = gsl_sf_bessel_Kn(2, z);
        float ratios[2] = {gsl_sf_bessel_Kn(0,z)/k2, gsl_sf_bessel_Kn(1,z)/k2};
        if (fwrite(ratios, sizeof(float), 2, tab) != 2) return 4;
    }
    double q[5];
    size_t count;
    const double length = GNEWT*6.2e9*MSUN/(CL*CL);
    while ((count = fread(q, sizeof(double), 5, in)) == 5) {
        struct parameters p;
        setConstParams(&p);
        p.distribution=p.MAXWELL_JUETTNER; p.dexter_fit=1;
        p.electron_density=q[0]; p.theta_e=q[1]; p.magnetic_field=q[2];
        p.nu=q[3]; p.observer_angle=acos(q[4]);
        double row[12] = {0}, g=2.3e11/p.nu;
        if (q[0] > 0 && q[2] > 0) {
            if (fabs(q[4]) < 1) {
                row[0]=j_nu_fit(&p,p.STOKES_I);
                row[1]=-j_nu_fit(&p,p.STOKES_Q);
                row[3]=j_nu_fit(&p,p.STOKES_V);
                double jp=sqrt(row[1]*row[1]+row[3]*row[3]);
                if (jp > row[0]*0.99) { row[1]*=row[0]*0.99/jp; row[3]*=row[0]*0.99/jp; }
                double planck = Bnu_inv(p.nu,p.theta_e)*pow(p.nu,3);
                if (planck > 0) for (int i=0;i<4;++i) row[i+4]=row[i]/planck*length;
                p.dexter_fit=0;
                row[8]=rho_nu_fit(&p,p.STOKES_Q)*length;
            }
            p.dexter_fit=0;
            row[10]=rho_nu_fit(&p,p.STOKES_V)*length;
            for (int i=0;i<4;++i) row[i]*=length*g*g*g;
        }
        row[11]=1;
        if (fwrite(row,sizeof(double),12,out) != 12) return 4;
    }
    int failed = count != 0 || ferror(in);
    failed |= fclose(in) != 0;
    failed |= fclose(out) != 0;
    failed |= fclose(tab) != 0;
    return failed ? 5 : 0;
}
