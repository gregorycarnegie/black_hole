import BlackHole.KernelFixture
import BlackHole.CudaGeodesic

def main : IO Unit := do
  IO.FS.writeFile "fixtures/kernels.sexp" BlackHole.KernelFixture.render
  IO.FS.writeFile "fixtures/kernels-branching.sexp" BlackHole.KernelFixture.renderBranching
  IO.FS.writeFile "fixtures/cuda-geodesic.sexp" BlackHole.CudaGeodesic.render
