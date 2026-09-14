import Solution

namespace TDLC.TransportTests

-- A genuinely multi-entry presentation exercises both recursive branches.
def twice : HomotopyPathI (fun n : Nat => n) (fun n : Nat => n) :=
  .seq (.beta (fun n => n)) (.seq (.sym (.beta (fun n => n))) (.nil _))

example (x y : Nat) (q : Path x y) :
    transportAlongPathI twice x y q =
      transportAlongPresented (.sym (.beta (fun n : Nat => n))) x y
        (transportAlongPresented (.beta (fun n : Nat => n)) x y q) := rfl

example {x y : Nat} (p : Path x y) :
    Path2 (transportAlongPathI twice x y (Path.ap (fun n => n) p))
      (Path.ap (fun n => n) p) := certifiedPathTransport twice p

example {x y : Nat} {q r : Path x y} (cells : Path2 q r) :
    Path2 (transportAlongPathI twice x y q) (transportAlongPathI twice x y r) :=
  transportAlongPathIRespects twice cells

example {x y : Nat} (p : Path x y) :
    Path2 (Path.ap (fun n => n) p ++ₚ evalHomotopyPathI twice y)
      (evalHomotopyPathI twice x ++ₚ Path.ap (fun n => n) p) :=
  certifiedPathNaturalityViaTransport twice p

-- Recovery accepts an arbitrary transport comparison, not just congruence paths.
example {x y : Nat} {q r : Path x y}
    (cells : Path2 (transportAlongPathI twice x y q) r) :
    Path2 (q ++ₚ evalHomotopyPathI twice y) (evalHomotopyPathI twice x ++ₚ r) :=
  recoverNaturalityFromPathTransport twice cells

end TDLC.TransportTests
