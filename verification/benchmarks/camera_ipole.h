#include "model_geodesics.h"
#include "model_tetrads.h"
#include "geodesics.h"
#include "ipolarray.h"
#include "geometry.h"
#include "tetrads.h"

static int camera_probe(const char *output)
{
    FILE *out = fopen(output, "wb");
    if (!out) return 3;
    double Xcam[4] = {0}, frame[4][4], cov[4][4];
    native_coord(params.rcam, params.thetacam, params.phicam, Xcam);
    if (make_camera_tetrad(Xcam, frame, cov)) return 4;
    double dsource = params.dsource*PC;
    double fovx = params.fovx_dsource*dsource/L_unit/MUAS_PER_RAD/params.rcam;
    double fovy = params.fovy_dsource*dsource/L_unit/MUAS_PER_RAD/params.rcam;
    for (int i=0; i<params.nx; ++i) for (int j=0; j<params.ny; ++j) {
        double row[24];
        init_XK(i,j,params.nx,params.ny,Xcam,params,fovx,fovy,row,row+4);
        for (int a=0;a<4;++a) for (int b=0;b<4;++b) row[8+4*a+b]=frame[a][b];
        if (fwrite(row,sizeof(double),24,out) != 24) return 5;
    }
    return fclose(out) ? 6 : 0;
}

static int outer_probe(const char *output)
{
    FILE *out=fopen(output,"wb"); if (!out) return 3;
    double Xcam[4]={0}, frame[4][4], cov[4][4], g[4][4];
    native_coord(params.rcam,params.thetacam,params.phicam,Xcam);
    if (make_camera_tetrad(Xcam,frame,cov)) return 4;
    gcov_func(Xcam,g);
    double fov=params.fovx_dsource*(params.dsource*PC)/L_unit/MUAS_PER_RAD/params.rcam;
    for (int pixel=0;pixel<16;++pixel) {
        int index=pixel*25599/15;
        double X[4],K[4],F[4],n[4];
        init_XK(index/160,index%160,160,160,Xcam,params,fov,fov,X,K);
        for(int i=0;i<4;++i) {n[i]=K[i]-frame[0][i];F[i]=frame[1][i];}
        project_out(F,n,g); normalize(F,g);
        int iteration;
        for(iteration=0;iteration<100000;++iteration) {
            double r,th;bl_coord(X,&r,&th);if(r<=120+1e-8)break;
            double dl=fmin(stepsize(X,K,0.000125),(r-120)/(1.1*fabs(r*K[1])));
            double Xi[4],Ki[4],Xm[4],Km[4],Fh[4],Fn[4];
            for(int i=0;i<4;++i){Xi[i]=X[i];Ki[i]=K[i];}
            push_photon(X,K,-dl,Xm,Km);
            double transfer_dl=-dl*L_unit*HPL/(ME*CL*CL);
            parallel_transport_vector(Xi,Xi,Xm,Ki,Ki,Km,F,F,Fh,transfer_dl/2);
            parallel_transport_vector(Xi,Xm,X,Ki,Km,K,F,Fh,Fn,transfer_dl);
            for(int i=0;i<4;++i)F[i]=Fn[i];
        }
        if(iteration==100000)return 5;
        if(fwrite(X,sizeof(double),4,out)!=4||fwrite(K,sizeof(double),4,out)!=4||fwrite(F,sizeof(double),4,out)!=4)return 6;
    }
    return fclose(out)?7:0;
}
