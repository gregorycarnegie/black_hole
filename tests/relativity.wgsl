// Runs the production WGSL functions, not a second CPU implementation.
@group(1) @binding(0) var<storage,read_write> checks: array<f32>;

fn matrix_error(a: mat4x4<f32>, b: mat4x4<f32>) -> f32 {
    var error = 0.0;
    for (var i=0u;i<4u;i++) { error = max(error,max(max(abs(a[i]-b[i]).x,abs(a[i]-b[i]).y),max(abs(a[i]-b[i]).z,abs(a[i]-b[i]).w))); }
    return error;
}

fn norm4(v: vec4<f32>) -> f32 { return max(max(abs(v.x),abs(v.y)),max(abs(v.z),abs(v.w))); }

fn trajectory(impact: f32) -> vec4<f32> {
    var metric = scene_metric(vec3<f32>(impact,0,100));
    var ray = init_ray(vec3<f32>(impact,0,100),vec3<f32>(0,0,-1),metric);
    let energy = ray.p.x;
    var error = 0.0;
    var screen_error = 0.0;
    for (var i=0u;i<3000u;i++) {
        if metric.clearance<0.002 { return vec4<f32>(1,error,screen_error,abs(ray.p.x-energy)); }
        let h = clamp(0.08*metric.clearance,0.0001,2.0)/length((metric.inv*ray.p).yzw);
        ray = step_ray(ray,h,metric);
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

@compute @workgroup_size(32)
fn check_physics(@builtin(global_invocation_id) id: vec3<u32>) {
    let i=id.x;
    if i>=20u { return; }
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
        passed=all(abs(cell)<vec4<f32>(100)) && cell.x>=length(cell.yzw);
    }
    if i==16u || i==17u {
        // Schwarzschild critical impact parameter is 3 sqrt(3) M.
        let ray=trajectory(select(4.8,5.6,i==17u));
        for(var c=0u;c<4u;c++) { checks[20u+4u*(i-16u)+c]=ray[c]; }
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
        passed=abs(kerr_radius(vec3<f32>(r,0,0),vec3<f32>(0,0,0.8))-1.6)<1.0e-6;
    }
    checks[i]=select(0.0,1.0,passed);
}
