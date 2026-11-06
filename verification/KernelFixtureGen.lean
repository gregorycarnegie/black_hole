import BlackHole.KernelFixture

def main : IO Unit := do
  IO.FS.writeFile "fixtures/kernels.sexp" BlackHole.KernelFixture.render
  IO.FS.writeFile "fixtures/kernels-branching.sexp" BlackHole.KernelFixture.renderBranching
