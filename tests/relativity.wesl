// Runs the production WESL functions, not a second CPU implementation.
@group(1) @binding(0) var<storage,read_write> checks: array<f32>;

fn matrix_error(a: mat4x4<f32>, b: mat4x4<f32>) -> f32 {
    var error = 0.0;
    for (var i=0u;i<4u;i++) { error = max(error,max(max(abs(a[i]-b[i]).x,abs(a[i]-b[i]).y),max(abs(a[i]-b[i]).z,abs(a[i]-b[i]).w))); }
    return error;
}

fn norm4(v: vec4<f32>) -> f32 { return max(max(abs(v.x),abs(v.y)),max(abs(v.z),abs(v.w))); }

// Matches the exact stationary, nonspinning configurations in BlackHole/Binary.lean.
fn verification_metric(pos: vec3<f32>, binary: bool) -> Metric {
    if binary {
        return add_kerr(add_kerr(flat_metric(),pos+vec3<f32>(7,0,0),0.5,vec3<f32>(0)),
            pos-vec3<f32>(7,0,0),0.5,vec3<f32>(0));
    }
    return add_kerr(flat_metric(),pos+vec3<f32>(7,0,0),1.0,vec3<f32>(0));
}

fn metric_derivative(m: Metric, i: u32) -> mat4x4<f32> {
    if i==1u { return m.dx; } if i==2u { return m.dy; } if i==3u { return m.dz; }
    return mat4x4<f32>();
}

fn connection(m: Metric, a: u32, b: u32, c: u32) -> f32 {
    let db=metric_derivative(m,b); let dc=metric_derivative(m,c);
    var value=0.0;
    for(var d=0u;d<4u;d++) {
        let dd=metric_derivative(m,d);
        value+=0.5*m.inv[d][a]*(db[c][d]+dc[b][d]-dd[c][b]);
    }
    return value;
}

// R_tt = ∂a Γ^a_tt + Γ^a_ab Γ^b_tt - Γ^a_tb Γ^b_ta for a stationary metric.
// Finite-difference connections use the production analytic metric derivatives.
fn vacuum_ricci_tt(binary: bool, epsilon: f32) -> f32 {
    let m=verification_metric(vec3<f32>(0),binary);
    var result=0.0;
    for(var a=0u;a<4u;a++) {
        if a>0u {
            var delta=vec3<f32>(0); delta[a-1u]=epsilon;
            let plus=verification_metric(delta,binary);
            let minus=verification_metric(-delta,binary);
            result+=(connection(plus,a,0u,0u)-connection(minus,a,0u,0u))/(2.0*epsilon);
        }
        for(var b=0u;b<4u;b++) {
            result+=connection(m,a,a,b)*connection(m,b,0u,0u)
                -connection(m,a,0u,b)*connection(m,b,0u,a);
        }
    }
    return result;
}

fn convergence_sample(sample: u32) {
    let pos=vec3<f32>(6,0,20);
    var metric=scene_metric(pos);
    var ray=init_ray(pos,vec3<f32>(0,0,-1),metric);
    if sample>0u {
        let steps=10u << (sample-1u);
        let h=40.0/f32(steps);
        for(var i=0u;i<steps;i++) {
            let step=step_ray(ray,h,metric);
            if !step.valid { checks[40u+12u*sample+3u]=-1.0; return; }
            ray=step.ray;
            metric=scene_metric(ray.pos);
            ray.screen=vec4<f32>(0.0,screen_frame(ray,metric)[0]);
        }
    }
    let base=40u+12u*sample;
    checks[base+3u]=1.0;
    let k=(metric.inv*ray.p).yzw;
    for(var i=0u;i<3u;i++) { checks[base+i]=ray.pos[i]; checks[base+8u+i]=k[i]; }
    for(var i=0u;i<4u;i++) { checks[base+4u+i]=ray.p[i]; }
    checks[base+11u]=abs(dot(ray.p,metric.inv*ray.p))/dot(ray.p,ray.p);
}

fn trajectory(impact: f32) -> vec4<f32> {
    var metric = scene_metric(vec3<f32>(impact,0,100));
    var ray = init_ray(vec3<f32>(impact,0,100),vec3<f32>(0,0,-1),metric);
    let energy = ray.p.x;
    var error = 0.0;
    var screen_error = 0.0;
    for (var i=0u;i<3000u;i++) {
        if metric.clearance<0.002 { return vec4<f32>(1,error,screen_error,abs(ray.p.x-energy)); }
        let h = clamp(0.08*metric.clearance,0.0001,2.0)/length((metric.inv*ray.p).yzw);
        let step = advance_ray(ray,h,metric);
        if !step.accepted { return vec4<f32>(-1,error,screen_error,1); }
        ray = step.ray;
        metric = scene_metric(ray.pos);
        error = max(error,abs(dot(ray.p,metric.inv*ray.p))/dot(ray.p,ray.p));
        screen_error = max(screen_error,abs(dot(ray.screen,metric.g*ray.screen)-1.0));
        screen_error = max(screen_error,abs(dot(ray.p,ray.screen))/length(ray.p));
        // Use the same per-step gauge reset as rendering. Without it, an
        // unobservable component along k diverges near the ingoing KS horizon.
        ray.screen = vec4<f32>(0.0,screen_frame(ray,metric)[0]);
        if length(ray.pos)>110.0 { return vec4<f32>(0,error,screen_error,abs(ray.p.x-energy)); }
    }
    return vec4<f32>(-1,error,screen_error,1);
}

@compute @workgroup_size(64)
fn check_physics(@builtin(global_invocation_id) id: vec3<u32>) {
    let i=id.x;
    if i>=35u { return; }
    if i>=29u {
        let pos=vec3<f32>(4,0,0);
        let metric=scene_metric(pos);
        let radial=Ray(pos,vec4<f32>(1,-3,0,0),vec4<f32>(0,0,1,0));
        var passed=false;
        if i==29u {
            let coarse=step_ray(radial,0.24,metric);
            let exact_r=4.0-0.24;
            let residual=abs(dot(coarse.ray.p,scene_metric(coarse.ray.pos).inv*coarse.ray.p))
                /dot(coarse.ray.p,coarse.ray.p);
            let refined=advance_ray(radial,0.24,metric);
            let expected_r=4.0-refined.h;
            let expected_p=-(expected_r+2.0)/(expected_r-2.0);
            passed=coarse.valid && residual<2.0e-4 && abs(coarse.ray.pos.x-exact_r)>1.0e-6*exact_r
                && refined.accepted && refined.h<0.24 && refined.error<=STEP_TOLERANCE
                && abs(refined.ray.pos.x-expected_r)<1.0e-6*expected_r
                && abs(refined.ray.p.y-expected_p)<1.0e-6*abs(expected_p);
        }
        if i==30u { passed = !step_ray(radial,4.0,metric).valid; }
        if i==31u {
            passed = !advance_ray(radial,0.0,metric).accepted
                && !advance_ray(radial,-1.0,metric).accepted;
        }
        if i==32u {
            var bad=radial; bad.screen.x=1.0e30;
            passed = !advance_ray(bad,0.24,metric).accepted;
        }
        if i==33u {
            var unchanged=true;
            var ray=radial;
            var remaining=0.5;
            for(var n=0u;n<100u && remaining>1.0e-7;n++) {
                let step=advance_ray(ray,min(0.24,remaining),scene_metric(ray.pos));
                if !step.accepted { unchanged=false; break; }
                remaining-=step.h; ray=step.ray;
            }
            let exact_r=3.5+remaining;
            let exact_p=-(exact_r+2.0)/(exact_r-2.0);
            passed=unchanged && remaining<1.0e-7 && abs(ray.pos.x-exact_r)<1.0e-6*exact_r
                && abs(ray.p.y-exact_p)<1.0e-6*abs(exact_p) && ray.p.x==radial.p.x;
        }
        if i==34u {
            let start=init_ray(vec3<f32>(6,0,20),vec3<f32>(0,0,-1),scene_metric(vec3<f32>(6,0,20)));
            var ray=start;
            var elapsed=0.0;
            var valid=true;
            var max_screen_error=0.0;
            for(var n=0u;n<4000u && elapsed<40.0;n++) {
                let metric=scene_metric(ray.pos);
                let step=advance_ray(ray,min(1.0,40.0-elapsed),metric);
                if !step.accepted || elapsed+step.h==elapsed { valid=false; break; }
                ray=step.ray; elapsed+=step.h;
                let m=scene_metric(ray.pos);
                max_screen_error=max(max_screen_error,abs(dot(ray.screen,m.g*ray.screen)-1.0));
                max_screen_error=max(max_screen_error,abs(dot(ray.p,ray.screen))/length(ray.p));
                ray.screen=vec4<f32>(0.0,screen_frame(ray,m)[0]);
            }
            let m=scene_metric(ray.pos);
            let base=112u;
            let k=(m.inv*ray.p).yzw;
            for(var j=0u;j<3u;j++) { checks[base+j]=ray.pos[j]; checks[base+8u+j]=k[j]; }
            for(var j=0u;j<4u;j++) { checks[base+4u+j]=ray.p[j]; }
            checks[base+3u]=max_screen_error;
            checks[base+11u]=elapsed;
            passed=valid && elapsed==40.0;
        }
        checks[100u+i-29u]=select(0.0,1.0,passed);
        return;
    }
    if i>=24u { convergence_sample(i-24u); return; }
    var passed=false;
    let identity=ETA*ETA;
    let x=vec3<f32>(3,2,4);
    let spin=vec3<f32>(0.4,-0.5,0.6);
    let m=add_kerr(flat_metric(),x,0.7,spin);
    let j=vec4<f32>(1,0.7,0.1,0.05);
    if i==0u { passed=matrix_error(flat_metric().g,ETA)==0.0; }
    if i==1u {
        let s=add_kerr(flat_metric(),vec3<f32>(10,0,0),1.0,vec3<f32>(0));
        passed=abs(s.g[0][0]+0.8)<1.0e-6 && abs(s.g[0][1]-0.2)<1.0e-6;
    }
    if i==2u { passed=matrix_error(m.g*m.inv,identity)<2.0e-6; }
    if i==3u {
        let b=add_kerr(m,x+vec3<f32>(8,0,0),0.5,-spin);
        let reversed=add_kerr(add_kerr(flat_metric(),x+vec3<f32>(8,0,0),0.5,-spin),x,0.7,spin);
        passed=b.valid && matrix_error(b.g*b.inv,identity)<2.0e-6 && matrix_error(b.inv,reversed.inv)<2.0e-6;
    }
    if i>=4u && i<=6u {
        var delta=vec3<f32>(0); delta[i-4u]=0.002;
        let plus=add_kerr(flat_metric(),x+delta,0.7,spin);
        let minus=add_kerr(flat_metric(),x-delta,0.7,spin);
        var analytic=m.dx;
        if i==5u { analytic=m.dy; } if i==6u { analytic=m.dz; }
        passed=matrix_error((plus.g-minus.g)*250.0,analytic)<6.0e-5;
    }
    if i==7u {
        let pro=add_kerr(flat_metric(),vec3<f32>(10,0,0),1.0,vec3<f32>(0,0,0.8));
        let retro=add_kerr(flat_metric(),vec3<f32>(10,0,0),1.0,vec3<f32>(0,0,-0.8));
        passed=pro.g[0][2]<0.0 && abs(pro.g[0][2]+retro.g[0][2])<1.0e-7;
    }
    if i==8u {
        let ray=init_ray(x,normalize(vec3<f32>(-1,0.2,-1)),m);
        passed=abs(dot(ray.p,m.inv*ray.p))<2.0e-6 && (m.inv*ray.p).x<0.0
            && abs(dot(ray.p,ray.screen))<2.0e-6 && abs(dot(ray.screen,m.g*ray.screen)-1.0)<2.0e-6;
    }
    if i==9u { passed=norm4(polarized_cell(j,0.0,vec3<f32>(0),2.0)-2.0*j)<1.0e-6; }
    if i==10u { passed=norm4(polarized_cell(j,2.0,vec3<f32>(0),3.0)-j*((1.0-exp(-6.0))/2.0))<1.0e-6; }
    if i==11u {
        let rotated=faraday_rotation(vec3<f32>(0,0,1),PI*0.5)*vec3<f32>(1,0,0);
        passed=length(rotated-vec3<f32>(0,1,0))<1.0e-6;
    }
    if i==12u {
        let converted=faraday_rotation(vec3<f32>(1,0,0),PI*0.5)*vec3<f32>(0,1,0);
        passed=length(converted-vec3<f32>(0,0,1))<1.0e-6;
    }
    if i==13u {
        let cell=polarized_cell(vec4<f32>(1,1,0,0),0.0,vec3<f32>(0,0,1),PI*0.5);
        passed=norm4(cell-vec4<f32>(PI*0.5,1,1,0))<1.0e-6;
    }
    if i==14u {
        let rho=vec3<f32>(2,3,5);
        let whole=polarized_cell(j,0.7,rho,2.0);
        let half=polarized_cell(j,0.7,rho,1.0);
        let composed=half+exp(-0.7)*vec4<f32>(half.x,faraday_rotation(rho,1.0)*half.yzw);
        passed=norm4(whole-composed)<2.0e-6;
    }
    if i==15u {
        let cell=polarized_cell(j,3.0,vec3<f32>(1000,300,-800),20.0);
        // A projected norm above one must not amplify the source polarization.
        let source=vec4<f32>(1.0,0.75*projected_evpa(2.0,0.0),0.0);
        let projected=polarized_cell(source,0.7,vec3<f32>(2,3,5),2.0);
        let gamma=spatial_metric(flat_metric());
        let tiny=spatial_unit(vec3<f32>(1.0e-12,0.0,0.0),gamma);
        let huge=spatial_unit(vec3<f32>(1.0e20,0.0,0.0),gamma);
        let zero=spatial_unit(vec3<f32>(0.0),gamma);
        passed=all(abs(cell)<vec4<f32>(100)) && cell.x>=length(cell.yzw)
            && source.x>=length(source.yzw) && projected.x>=length(projected.yzw)
            && abs(dot(tiny,gamma*tiny)-1.0)<1.0e-6
            && abs(dot(huge,gamma*huge)-1.0)<1.0e-6 && all(zero==vec3<f32>(0.0));
    }
    if i==16u || i==17u {
        // Schwarzschild critical impact parameter is 3 sqrt(3) M.
        let ray=trajectory(select(4.8,5.6,i==17u));
        for(var c=0u;c<4u;c++) { checks[24u+4u*(i-16u)+c]=ray[c]; }
        passed=ray.x==select(1.0,0.0,i==17u) && ray.y<2.0e-4 && ray.z<0.002 && ray.w<1.0e-7;
    }
    if i==18u {
        // Faraday rotation/conversion are noncommuting: foreground comes first.
        let front=faraday_rotation(vec3<f32>(0,0,1),PI*0.5);
        let back=faraday_rotation(vec3<f32>(1,0,0),PI*0.5);
        passed=length(front*back*vec3<f32>(0,1,0)-vec3<f32>(0,0,1))<1.0e-6;
    }
    if i==19u {
        let r=sqrt(1.6*1.6+0.8*0.8);
        let pos=vec3<f32>(r,0,0);
        passed=abs(disk_radius(pos,0.8,false)-1.6)<1.0e-6
            && abs(disk_radius(pos,-0.8,false)-1.6)<1.0e-6
            && abs(disk_radius(pos,0.8,true)-r)<1.0e-6
            && abs(disk_radius(pos+vec3<f32>(0,7,0),0.8,false)-1.6)<1.0e-6
            && disk_radius(vec3<f32>(0,10,0),0.8,false)<0.001;
    }
    if i==20u {
        // Cancellation in the direct quadratic root would lose this radius.
        passed=abs(kerr_radius(vec3<f32>(0,0,0.0001),vec3<f32>(0,0,0.8))-0.0001)<1.0e-8;
    }
    if i==21u {
        let first=init_ray(x,vec3<f32>(0,0,-1),flat_metric());
        let second=init_ray(x,vec3<f32>(1,0,0),flat_metric());
        passed=dot(first.p,ETA*first.p)==0.0 && dot(second.p,ETA*second.p)==0.0
            && first.p.x==second.p.x && length(first.p-second.p)>1.0;
    }
    if i==22u || i==23u {
        let binary=i==23u;
        let coarse=vacuum_ricci_tt(binary,0.02);
        let fine=vacuum_ricci_tt(binary,0.01);
        checks[32u+2u*(i-22u)]=coarse; checks[33u+2u*(i-22u)]=fine;
        let expected=select(0.0,4.0/3087.0,binary);
        passed=abs(coarse-expected)<2.0e-6 && abs(fine-expected)<2.0e-6;
    }
    checks[i]=select(0.0,1.0,passed);
}
