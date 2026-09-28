import Http1

/-!
`http1`: the proved framing spec, made runnable.

    http1 frame < request.bin      reads raw request bytes on stdin, prints the framing verdict
                                   (reject | chunked | length:N | until_close)

The verdict comes from `Http1.frame`, the function `no_desync` is proved about. This is the reference
reading the differential harness compares every other parser against.
-/

open Http1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["frame"] =>
    let stdin ← IO.getStdin
    let raw ← stdin.readBinToEnd
    IO.println (Parse.verdict raw.toList)
    return 0
  | _ =>
    IO.eprintln "usage: http1 frame < request.bin"
    return 2
