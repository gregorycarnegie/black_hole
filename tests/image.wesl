import package::geodesic::{Ray, scene_metric, advance_ray_gauge, screen_frame, kerr_radius};
import package::snapshot::{sample_snapshot, snapshot_header};
import package::thermal::thermal_coefficients;
import package::polarized_transfer::transfer_cell;

struct ImageSeed { position: vec4<f32>, momentum: vec4<f32>, screen: vec4<f32>, jones: vec4<f32> }
@group(3) @binding(0) var<storage,read> seeds: array<ImageSeed>;
@group(3) @binding(1) var<uniform> settings: vec4<f32>; // cell fraction, step budget, count, Jy scale
@group(3) @binding(2) var<storage,read_write> pixels: array<vec4<f32>>;

fn radius_rate(pos: vec3<f32>, k: vec3<f32>, r: f32) -> f32 {
    let a=vec3<f32>(0.0,0.9375,0.0);
    return dot((r*pos+(dot(a,pos)/r)*a)/(2.0*r*r-dot(pos,pos)+dot(a,a)),k);
}

fn grid_step(pos: vec3<f32>, k: vec3<f32>, r: f32, dr: f32) -> f32 {
    let a=0.9375;
    let s=sqrt(dot(pos.xz,pos.xz)/(r*r+a*a));
    let dtheta=-(k.y/r-pos.y*dr/(r*r))/max(s,1.0e-8);
    let th=atan2(s,pos.y/r);
    var lo=0.0; var hi=1.0;
    for(var i=0u;i<25u;i++) {
        let mid=0.5*(lo+hi);
        let angle=3.141592653589793*mid+0.35*sin(6.283185307179586*mid);
        if angle<th {lo=mid;} else {hi=mid;}
    }
    let x2=0.5*(lo+hi);
    let dth=3.141592653589793*(1.0+0.7*cos(6.283185307179586*x2));
    let aa=-r*pos.z-a*pos.x; let bb=r*pos.x-a*pos.z;
    let da=-dr*pos.z-r*k.z-a*k.x; let db=dr*pos.x+r*k.x-a*k.z;
    let dphi=(bb*da-aa*db)/max(aa*aa+bb*bb,1.0e-20);
    let rates=abs(vec3<f32>(dr/r,dtheta/dth,dphi))/snapshot_header.spacing.xyz;
    return settings.x/max(max(rates.x,rates.y),max(rates.z,1.0e-8));
}

fn camera_stokes(s: vec4<f32>, j: vec4<f32>) -> vec4<f32> {
    let n11=j.x*j.x*(s.x+s.y)+j.y*j.y*(s.x-s.y)+2.0*j.x*j.y*s.z;
    let n22=j.z*j.z*(s.x+s.y)+j.w*j.w*(s.x-s.y)+2.0*j.z*j.w*s.z;
    let u=j.x*j.z*(s.x+s.y)+j.y*j.w*(s.x-s.y)+(j.x*j.w+j.y*j.z)*s.z;
    // ipole qu_conv=0 exports North EVPA, negating camera-frame Q and U.
    return vec4<f32>(0.5*(n11+n22),-0.5*(n11-n22),-u,(j.x*j.w-j.y*j.z)*s.w);
}

@compute @workgroup_size(32)
fn render_snapshot(@builtin(global_invocation_id) id: vec3<u32>) {
    if id.x>=u32(settings.z) {return;}
    let seed=seeds[id.x];
    var ray=Ray(seed.position.xyz,seed.momentum,seed.screen);
    var foreground=mat4x4<f32>(vec4<f32>(1,0,0,0),vec4<f32>(0,1,0,0),vec4<f32>(0,0,1,0),vec4<f32>(0,0,0,1));
    var intensity=vec4<f32>(0.0);
    var next_h=500.0; var affine=seed.position.w; var max_null=0.0;
    var status=3u; var steps=0u; var last_h=0.0; var last_actual=0.0; var last_error=0.0;
    for(var iteration=0u;iteration<u32(settings.y);iteration++) {
        steps=iteration;
        let m=scene_metric(ray.pos); let k=m.inv*ray.p;
        let r=kerr_radius(ray.pos,vec3<f32>(0,0.9375,0));
        let dr=radius_rate(ray.pos,k.yzw,r);
        if m.clearance<=0.0001 {status=1u;break;}
        if r>100.0 && dr>0.0 {status=2u;break;}
        if affine>21000.0 {break;}
        var h=min(next_h,min(0.05*r/max(length(k.yzw),1.0e-20),0.25*m.clearance/max(abs(dr),1.0e-20)));
        if r<101.0 {h=min(h,grid_step(ray.pos,k.yzw,r,dr));}
        else {h=min(h,max(0.5,(r-100.0)/max(abs(dr),1.0e-8)));}
        last_h=h;
        let step=advance_ray_gauge(ray,h,m,true);
        last_actual=step.h;last_error=step.error;
        if !step.accepted {status=4u;break;}
        let middle=Ray(0.5*(ray.pos+step.ray.pos),0.5*(ray.p+step.ray.p),0.5*(ray.screen+step.ray.screen));
        let rm=kerr_radius(middle.pos,vec3<f32>(0,0.9375,0));
        let sm=sqrt(dot(middle.pos.xz,middle.pos.xz)/(rm*rm+0.9375*0.9375));
        if rm<100.0 && sm>sin(0.0174) {
            let plasma=sample_snapshot(middle.pos);
            if !plasma.valid {status=5u;break;}
            if plasma.emitting && plasma.physical.x>0.0 {
                let metric=scene_metric(middle.pos);
                let normalization=seed.momentum.x/middle.p.x;
                let future=-(metric.inv*middle.p)*normalization;
                let energy=dot(middle.p,plasma.velocity)*normalization;
                let bcov=metric.g*plasma.magnetic;
                let bsq=dot(plasma.magnetic,bcov);
                let mu=clamp(dot(future,bcov)/max(energy*sqrt(abs(bsq)),1.0e-20),-1.0,1.0);
                let local=thermal_coefficients(plasma.physical.xyz,2.3e11*energy,mu);
                if !local.valid || !(energy>0.0) {status=6u;break;}
                var c=local.coefficients;
                let frame=screen_frame(middle,metric);
                let e1=vec4<f32>(0.0,frame[0]); let e2=vec4<f32>(0.0,-frame[1]);
                let f1=e1+future*(dot(e1,metric.g*plasma.velocity)/energy);
                let f2=e2+future*(dot(e2,metric.g*plasma.velocity)/energy);
                let bproj=vec2<f32>(dot(f1,bcov),dot(f2,bcov));
                let b2=dot(bproj,bproj);
                var rotation=vec2<f32>(1,0);
                if b2>1.0e-20 {rotation=vec2<f32>(bproj.y*bproj.y-bproj.x*bproj.x,-2.0*bproj.x*bproj.y)/b2;}
                c.emission=vec4<f32>(c.emission.x,c.emission.y*rotation,c.emission.w);
                c.absorption=vec4<f32>(c.absorption.x,c.absorption.y*rotation,c.absorption.w);
                c.faraday=vec3<f32>(c.faraday.x*rotation,c.faraday.z);
                let cell=transfer_cell(vec4<f32>(0.0),c,energy*step.h/normalization);
                if !cell.valid {next_h=0.5*step.h;continue;}
                intensity+=foreground*cell.stokes;
                foreground=foreground*cell.transmission;
            }
        }
        affine+=step.h*ray.p.x/seed.momentum.x;
        ray=step.ray;
        // Homogeneous momentum scaling changes affine parameter, not the ray curve.
        // Re-gauging keeps the physical screen bounded near the coordinate horizon.
        let endpoint_metric=scene_metric(ray.pos);
        ray.screen=vec4<f32>(0.0,screen_frame(ray,endpoint_metric)[0]);
        let momentum_scale=max(max(abs(ray.p.x),abs(ray.p.y)),max(abs(ray.p.z),abs(ray.p.w)));
        ray.p/=momentum_scale;
        let metric=scene_metric(ray.pos);
        max_null=max(max_null,abs(dot(ray.p,metric.inv*ray.p))/max(dot(ray.p,ray.p),1.0e-10));
        next_h=momentum_scale*step.h*clamp(0.9*pow(5.0e-8/max(step.error,1.0e-20),0.2),0.5,2.0);
    }
    pixels[4u*id.x]=settings.w*camera_stokes(intensity,seed.jones);
    pixels[4u*id.x+1u]=vec4<f32>(f32(steps),f32(status),max_null,affine);
    let final_metric=scene_metric(ray.pos);
    pixels[4u*id.x+2u]=vec4<f32>(ray.pos,final_metric.clearance);
    pixels[4u*id.x+3u]=vec4<f32>(last_h,last_actual,last_error,ray.p.x);
}
