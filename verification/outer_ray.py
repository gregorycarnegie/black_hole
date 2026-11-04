"""Binary64 Cartesian Kerr RK4 for the emission-free camera-to-120 r_g segment."""

import numpy as np


def geometry(x):
    a = np.array([0., 0.9375, 0.])
    ax, q = x @ a, np.sum(x*x, axis=-1)-a@a
    r = np.sqrt((q+np.sqrt(q*q+4*ax*ax))/2)
    r2, den = r*r, r**4+ax*ax
    h = r**3/den
    ell = np.column_stack((np.ones(len(x)), (r[:,None]*x-np.cross(a,x)+(ax/r)[:,None]*a)/(r2+a@a)[:,None]))
    eta = np.diag([-1.,1,1,1])
    g = eta+2*h[:,None,None]*ell[:,:,None]*ell[:,None,:]
    raised = ell @ eta
    inv = eta-2*h[:,None,None]*raised[:,:,None]*raised[:,None,:]
    dr = (r[:,None]*x+(ax/r)[:,None]*a)/(2*r2-np.sum(x*x,axis=-1)+a@a)[:,None]
    dg = np.empty((len(x),3,4,4))
    for j in range(3):
        basis = np.eye(3)[j]
        dh = h*(3*dr[:,j]/r-(4*r**3*dr[:,j]+2*ax*a[j])/den)
        dn = dr[:,j,None]*x+r[:,None]*basis-np.cross(a,basis)+(a[j]/r-ax*dr[:,j]/r2)[:,None]*a
        dl = np.column_stack((np.zeros(len(x)), (dn-ell[:,1:]*(2*r*dr[:,j])[:,None])/(r2+a@a)[:,None]))
        dg[:,j] = 2*dh[:,None,None]*ell[:,:,None]*ell[:,None,:]+2*h[:,None,None]*(dl[:,:,None]*ell[:,None,:]+ell[:,:,None]*dl[:,None,:])
    return r, g, inv, dg


def rhs(state):
    _, _, inv, dg = geometry(state[:,:3])
    p, f = state[:,3:7], state[:,7:11]
    k = np.einsum("nij,nj->ni", inv,p)
    force = np.column_stack((np.zeros(len(p)),0.5*np.einsum("ni,naij,nj->na",k,dg,k)))
    dgk = np.einsum("na,naij->nij",k[:,1:],dg)
    dgf = np.einsum("na,naij->nij",f[:,1:],dg)
    contracted = np.column_stack((np.zeros(len(p)),np.einsum("ni,naij,nj->na",k,dg,f)))
    df = -0.5*np.einsum("nij,nj->ni",inv,np.einsum("nij,nj->ni",dgk,f)+np.einsum("nij,nj->ni",dgf,k)-contracted)
    return np.column_stack((k[:,1:],force,df))


def trace(seeds, fraction):
    state = np.column_stack((seeds[:,0,:3],seeds[:,1],seeds[:,2])).astype(float)
    affine=np.zeros(len(seeds))
    for iteration in range(1000):
        r, _, inv, _ = geometry(state[:,:3])
        active = r>120+1e-8
        if not active.any(): break
        s=state[active]
        k=np.einsum("nij,nj->ni",inv[active],s[:,3:7])
        # Use a conservative radial-speed bound in this admitted outer segment.
        h=np.minimum(fraction*r[active],(r[active]-120)/1.1)[:,None]
        b1=rhs(s);b2=rhs(s+h*b1/2);b3=rhs(s+h*b2/2);b4=rhs(s+h*b3)
        affine[active]+=h[:,0]
        state[active]=s+h/6*(b1+2*b2+2*b3+b4)
    else: raise ValueError("Outer segment exceeded its step budget")
    r,g,inv,_=geometry(state[:,:3])
    p,f=state[:,3:7],state[:,7:11]
    k=np.einsum("nij,nj->ni",inv,p)
    null=np.max(np.abs(np.einsum("ni,ni->n",p,k)))
    norm=np.max(np.abs(np.einsum("ni,nij,nj->n",f,g,f)-1))
    transverse=np.max(np.abs(np.einsum("ni,ni->n",p,f)))
    if not np.isfinite(state).all() or max(null,norm,transverse)>1e-9:
        raise ValueError(f"Outer transport residuals: {null}, {norm}, {transverse}")
    result=seeds.copy()
    result[:,0,:3],result[:,1]=state[:,:3],p
    result[:,0,3]=affine
    # The gauge-fixed GPU transport starts with f^0=0.
    result[:,2]=f-k*(f[:,0]/k[:,0])[:,None]
    return result, {"steps":iteration,"max_affine_length":float(affine.max()),"max_null":float(null),"max_screen_norm_error":float(norm),"max_transversality":float(transverse)}
