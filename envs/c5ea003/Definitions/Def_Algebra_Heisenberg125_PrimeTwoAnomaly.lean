-- Prove2me | Definitions.Def_Algebra_Heisenberg125_PrimeTwoAnomaly
-- name    : Algebra_Heisenberg125_PrimeTwoAnomaly
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:34:01.968056+00:00
-- url     : https://prove2.me/theorems/9cfabee0-7415-426d-9315-e23ee09f97e3
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_PrimeTwoAnomaly
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.PrimeTwoAnomaly`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/PrimeTwoAnomaly.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
/-
# The oddness hypothesis is necessary: `d(H_8) ≥ 4 > 3·2 - 3`

Godara and Sarkar conjecture `d(H_{p^3}) = 3p - 3` for every *odd* prime `p`.
The group `Heis 2` of order `8` (which has exponent `4`, not `2`, so it is not
the exponent-`p` Heisenberg group) shows that the oddness is not cosmetic: the
sequence `y · (xy)^3` is product-one-free of length `4 > 3 = 3·2 - 3`.

This also pins down where our odd-`p` arguments break: for `p = 2` one has
`p ∤ binom p 2`, so `p` equal elements in one coset of the centre need not
multiply to a central element, and `2` is not invertible, so the cocycle
straightening `c ↦ c - (m/2) a²` of `Algebra.Heisenberg125.LineBound` is
unavailable.
-/

namespace Heisenberg125

namespace Heis

/-- `y = (0,1,0)` in `Heis 2`. -/
private def g2 : Heis 2 := ⟨0, 1, 0⟩
/-- `xy = (1,1,0)` in `Heis 2`. -/
private def h2 : Heis 2 := ⟨1, 1, 0⟩

/-- The product-one-free sequence `y (xy)^3` of length `4` over `Heis 2`. -/
def anomalySeq : List (Heis 2) := [g2] ++ List.replicate 3 h2




end Heis

end Heisenberg125


