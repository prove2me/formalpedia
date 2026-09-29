-- Prove2me | Theorems.Thm_AlmostLossless_card_sepSet
-- name    : AlmostLossless.card_sepSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:45.84578+00:00
-- url     : https://prove2.me/theorems/c38cd2db-5967-4a93-802b-85b7d42b2b8f
-- title:
--   Exact count of separating codebooks:
-- statement:
--   **Exact count of separating codebooks**:
--   `M^{|D|} · |{H : H y ≠ H x for all y ∈ D}| = (M-1)^{|D|} · M^{|α|}`.
--
--   ```lean
--   theorem AlmostLossless.card_sepSet(x : α) (D : Finset α) (hx : x ∉ D) :
--       M ^ D.card * (sepSet D x M).card = (M - 1) ^ D.card * M ^ Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessExact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessExact.lean#L105

-- Thm stub generated from Geometry/AlmostLosslessExact.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_AlmostLosslessExact
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

open AlmostLossless

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}

theorem AlmostLossless.card_sepSet(x : α) (D : Finset α) (hx : x ∉ D) :
    M ^ D.card * (sepSet D x M).card = (M - 1) ^ D.card * M ^ Fintype.card α := by sorry
