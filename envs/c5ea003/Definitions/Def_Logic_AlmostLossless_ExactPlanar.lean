-- Prove2me | Definitions.Def_Logic_AlmostLossless_ExactPlanar
-- name    : Logic_AlmostLossless_ExactPlanar
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:46:47.356773+00:00
-- url     : https://prove2.me/theorems/44036293-eb9a-45ae-8fb8-00c5203386c0
-- title:
--   Aether Catalog definitions — Logic_AlmostLossless_ExactPlanar
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AlmostLossless.ExactPlanar`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AlmostLossless/ExactPlanar.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing

/-!
# The exact failure probability of the planar inner-product compressor

The union bound of `AlmostLossless.collisionProb_le` charges one `1/p` per pair
of typical words.  In dimension `k = 2` the truth is *exactly* computable, and
it is strictly better whenever two pairs of typical words happen to differ by
proportional vectors: only the **projective directions** of the difference set
matter.

For a seed `a ∈ (ZMod p)²` the hash `x ↦ ⟨a,x⟩` confuses `x` and `y` iff `a`
lies on the line orthogonal to `x - y`.  Distinct projective directions give
lines meeting only at the origin, so the bad seeds form a "pencil" of `d` lines
through `0`:

`#{bad seeds} = 1 + d·(p-1)`, i.e. `P(failure) = (1 + d(p-1))/p²`,

where `d` is the number of distinct directions among the differences of typical
words (`AlmostLossless.exact_card_collides_planar`).  Since `d ≤ |T|(|T|-1)/2`,
this refines the union bound, and it is an *equality*, so the falsifiability
gate of the research thread is met with an exact figure rather than a bound.

This is a small bridge between finite projective geometry over `𝔽_p` and the
Monte-Carlo analysis of a compressor.
-/

namespace AlmostLossless

open Finset

section Planar

variable {p : ℕ} [Fact p.Prime]

/-! ## Elementary identities for the inner-product hash -/



/-- The line of seeds orthogonal to `z`. -/
def orth (z : Fin 2 → ZMod p) : Finset (Fin 2 → ZMod p) := {a | dotHom z a = 0}




/-! ## The pencil of bad seeds -/


/-! ## Exact failure probability of the planar compressor -/



end Planar

/-! ## A worked example, cross-checked by exhaustive computation

The hypotheses of `exact_card_collides_planar` are satisfiable: here is a
concrete typical set over `ZMod 11`.  The count predicted by the theorem
(`1 + 3·(11-1) = 31` bad seeds out of `121`) is confirmed independently by
brute-force evaluation, which also shows the theorem is not vacuous. -/

section Example

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- A three-element typical set in `(ZMod 11)²`. -/
def exampleTypical : Finset (Fin 2 → ZMod 11) := {![1, 0], ![0, 1], ![2, 3]}

/-- Representatives of the three projective directions of its difference set. -/
def exampleDirections : Finset (Fin 2 → ZMod 11) := {![1, 10], ![10, 8], ![9, 9]}




end Example

end AlmostLossless


