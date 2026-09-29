-- Prove2me | Theorems.Thm_AlmostLossless_card_sepSet_insert
-- name    : AlmostLossless.card_sepSet_insert
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:35.565459+00:00
-- url     : https://prove2.me/theorems/88ffc007-7e27-4414-bc12-ef92e5226419
-- title:
--   The one-step recursion: adding one competitor multiplies the number of
-- statement:
--   The one-step recursion: adding one competitor multiplies the number of
--   separating codebooks by `(M-1)/M`.
--
--   ```lean
--   theorem AlmostLossless.card_sepSet_insert{D : Finset α} {x a : α} (ha : a ∉ D) (hax : a ≠ x) :
--       M * (sepSet (insert a D) x M).card = (M - 1) * (sepSet D x M).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessExact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessExact.lean#L36

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

theorem AlmostLossless.card_sepSet_insert{D : Finset α} {x a : α} (ha : a ∉ D) (hax : a ≠ x) :
    M * (sepSet (insert a D) x M).card = (M - 1) * (sepSet D x M).card := by sorry
