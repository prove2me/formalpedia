-- Prove2me | Definitions.Def_Geometry_AlmostLosslessExact
-- name    : Geometry_AlmostLosslessExact
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:42:02.44364+00:00
-- url     : https://prove2.me/theorems/1a3298ae-f7d6-412b-8d8f-1bb80659bf79
-- title:
--   Aether Catalog definitions — Geometry_AlmostLosslessExact
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AlmostLosslessExact`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AlmostLosslessExact.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# The exact failure probability of random hashing

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`AlmostLosslessDecoder` gives the upper bound `P[failure] ≤ (|S|-1)/M` and
`AlmostLosslessConverse` the Bonferroni lower bound `P[failure] ≥ (|S|-1)/(2M)`.
Here we compute the quantity **exactly**:

`AlmostLossless.card_sepSet` :  `M^k · |{H : H separates x from D}| = (M-1)^k · M^{|α|}`  (`k = |D|`),

whence `AlmostLossless.failure_prob_exact`:

`P[failure at x] = 1 - (1 - 1/M)^{|S|-1}`.

Both previously proved bounds are corollaries of this identity in the regime
they cover, and the measured values of `AlmostLosslessLabNotes` (`3/4`, `5/9`,
`7/16`, `15/64`, `31/256`) are exactly its values at `|S| = 3`.

The proof is an explicit bijection
`{H separating x from D ∪ {a}} × Fin M  ≃  Σ_{H separating x from D} (Fin M \ {H x})`,
given by `(H, v) ↦ ⟨update H a v, H a⟩`, iterated by induction on `D`.
-/

namespace AlmostLossless

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}

/-- Codebooks that separate `x` from every element of `D`. -/
def sepSet (D : Finset α) (x : α) (M : ℕ) : Finset (α → Fin M) :=
  univ.filter (fun H => ∀ y ∈ D, H y ≠ H x)






end AlmostLossless


