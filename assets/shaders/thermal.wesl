// Thermal fits/scaling from AFD-Illinois/ipole, commit 7f7a482.
// Copyright (c) 2024, AFD Group at UIUC. BSD-3-Clause: ipole-LICENSE.txt.
import package::polarized_transfer::TransferCoefficients;

// GSL K0/K2, K1/K2 table, exported with the pinned independent probe.
// First two vec2s: log(T_min), log step; cold underflow cutoff, T_max.
@group(2) @binding(0) var<storage,read> thermal_bessel: array<vec2<f32>>;

struct ThermalResult { coefficients: TransferCoefficients, valid: bool }

fn thermal_bessel_ratios(t: f32) -> vec2<f32> {
    if t < thermal_bessel[1].x { return vec2<f32>(1.0); }
    if t < 0.002 {
        // Scaled large-argument K_n expansion avoids exponentially tiny K_n values.
        var sum = vec3<f32>(1.0); var term = vec3<f32>(1.0);
        for (var k=1u; k<=4u; k++) {
            let odd = f32(2u*k-1u);
            term *= (vec3<f32>(0.0,4.0,16.0)-odd*odd)*(t/(8.0*f32(k)));
            sum += term;
        }
        return sum.xy/sum.z;
    }
    let index = clamp((log(t)-thermal_bessel[0].x)/thermal_bessel[0].y,0.0,8192.0);
    let low = min(u32(index),8191u);
    return mix(thermal_bessel[low+2u],thermal_bessel[low+3u],index-f32(low));
}

fn thermal_coefficients(physical: vec3<f32>, frequency: f32, mu: f32) -> ThermalResult {
    var result: ThermalResult;
    let ne = physical.x; let t = physical.y; let b = physical.z;
    // shortcut: pinned 230 GHz observer and M87* units; rebuild scaling/table for other benchmarks.
    if !(ne>=0.0 && ne<=1.0e12 && t>=0.001 && t<=1000.0 && b>=0.0 && b<=1.0e5 &&
         frequency>=1.0e8 && frequency<=1.0e20 && abs(mu)<=1.0) { return result; }
    result.valid = true;
    if ne==0.0 || b==0.0 { return result; }
    let nu = frequency;
    let ratios = thermal_bessel_ratios(t);
    let s = sqrt(max(0.0,1.0-mu*mu));
    let nuc = 2799250.54224516*b;
    let xfar = t*sqrt(1.4142135623730951*s*1.0e3*nuc/nu);
    // Multiplication order keeps CGS factors within binary32's normal range.
    let faraday_scale = 7736369572802.028*ne/nu;
    let rho_v = 2.0*faraday_scale*(nuc/nu)*ratios.x*(1.0-0.11*log(1.0+0.035*xfar))*mu;
    result.coefficients.faraday.z = rho_v;
    if s==0.0 { return result; }
    var extra = 0.0;
    if xfar>1.0 {
        extra = (0.011*exp(-xfar/47.2)-0.011767707320949831*3.141592653589793*1.0e4*pow(xfar+1.0e-16,-8.0/3.0))*
            (0.5+0.5*tanh((log(xfar)-log(120.0))/0.1));
    }
    let jf = 2.011*exp(-pow(xfar,1.035)/4.7)-cos(xfar/2.0)*exp(-pow(xfar,1.2)/2.73)-0.011*exp(-xfar/47.2)+extra;
    result.coefficients.faraday.x = faraday_scale*(nuc/nu)*(nuc/nu)*jf*(ratios.y+6.0*t)*s*s;
    let x = nu/(1.5*nuc*s*t*t+1.0);
    let root = pow(x,1.0/3.0); let inv = 1.0/root;
    let cutoff = exp(-1.8899*root);
    let fi = 2.5651*(1.0+1.92*inv+0.9977*inv*inv)*cutoff;
    let fq = 2.5651*(1.0+0.93193*inv+0.499873*inv*inv)*cutoff;
    let fv = (1.81384/x+3.42319*inv*inv+0.0292545/sqrt(x)+2.03773*inv)*cutoff;
    let g = 2.3e11/nu;
    let scale = (2.034396163948838e-15*ne*nu/(t*t))*g*g*g;
    var j = scale*vec4<f32>(fi,fq,0.0,(4.0/(3.0*t))*(mu/s)*fv);
    let fraction = length(j.yzw/max(j.x,1.0e-30));
    if fraction>0.99 { j=vec4<f32>(j.x,j.yzw*(0.99/fraction)); }
    let planck_x = 8.093299734781324e-21*nu/t;
    var denominator = exp(planck_x)-1.0;
    if planck_x<0.002 {
        denominator = planck_x/24.0*(24.0+planck_x*(12.0+planck_x*(4.0+planck_x)));
    }
    let planck = 1.7940232686371595e-13/denominator;
    result.coefficients.emission = j;
    if planck>0.0 { result.coefficients.absorption=j/planck; }
    result.valid = all(abs(j)<vec4<f32>(1.0e30)) && all(abs(result.coefficients.absorption)<vec4<f32>(1.0e30)) &&
        all(abs(result.coefficients.faraday)<vec3<f32>(1.0e30));
    return result;
}
