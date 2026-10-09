import Lake

/-! Lake entry point for repository source, import-boundary, and proof checks. -/

def main (args : List String) : IO UInt32 := do
  let child ←
    IO.Process.spawn
      {
        cmd := "python3"
        args := #["scripts/lint.py"] ++ args.toArray
      }
  child.wait
