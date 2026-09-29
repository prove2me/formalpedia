-- Prove2me | Theorems.Thm_BonferroniMarginals_jointFail_card_univ_ne
-- name    : BonferroniMarginals.jointFail_card_univ_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:26:53.966977+00:00
-- url     : https://prove2.me/theorems/03db4142-1c46-443b-8056-49176204fe96
-- title:
--   The top-order marginal differs: the full intersection has one point in
-- statement:
--   **The top-order marginal differs**: the full intersection has one point in
--   the first family and two in the second.
--
--   ```lean
--   theorem BonferroniMarginals.jointFail_card_univ_ne(hk : 0 < k) :
--       (jointFail (plainFam k) univ).card ≠ (jointFail (parityFam k) univ).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean#L229

-- Thm stub generated from MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_MarginalIndeterminacy

/-!
# Every marginal order below `k` is insufficient for `k` sets

`MarginalIndeterminacy.lean` exhibits three sets whose first- and second-order
marginals coincide but whose unions differ, showing that the Bonferroni
machinery can never be upgraded to an identity.  That example leaves open the
obvious escape route: *maybe order `3`, or order `17`, always suffices.*

This file closes the escape route completely.  For **every** `k ≥ 1` we build
two families of `k` sets, `plainFam k` and `parityFam k`, on a common ground set
of `2^(k+1)` points such that

* all joint marginals of order `< k` agree —
  `jointFail_card_eq_of_ne_univ`: `|⋂_{i ∈ T} Aᵢ| = |⋂_{i ∈ T} Bᵢ|` for every
  `T ≠ univ`;
* the top-order marginal differs (`jointFail_card_univ_ne`), and
* the unions differ (`card_cover_ne`), one being odd and the other even.

Hence `marginal_order_lt_insufficient`: no functional of the marginals of order
`< k` can compute the union of `k` sets, for any `k ≥ 1`.  Together with
`card_cover_eq_of_all_inf_card_eq` (inclusion–exclusion), the marginal order
threshold for a family of `k` sets is **exactly `k`**.

## The construction

Ground set `Ω = Finset (Fin k) × Bool`: two labelled copies of every subset of
`Fin k`.

* `plainFam k i = {(S, false) | i ∈ S}` — one copy of each subset containing `i`.
* `parityFam k i = {(S, b) | i ∈ S, |S| ≡ k (mod 2)}` — *two* copies of the
  subsets of the correct size parity.

Writing `w(S)` for the number of ground points sitting over `S`, the two
families have weight functions `1` and `1 + (−1)^{k−|S|}`; the perturbation
`δ(S) = (−1)^{k−|S|}` has vanishing "upper sums" `∑_{S ⊇ T} δ(S) = 0` for all
`T ≠ univ`, by the alternating binomial identity — and this is exactly the
statement that all marginals of order `< k` are unchanged.  The perturbation is
invisible below order `k` and flips the parity of the union.
-/

open BonferroniMarginals

open Finset

/-! ## Joint marginals of arbitrary order -/


/-! ## Counting subsets with a prescribed size parity -/


/-! ## Supersets of a fixed set -/

variable {k : ℕ}




/-! ## The two families -/

theorem BonferroniMarginals.jointFail_card_univ_ne(hk : 0 < k) :
    (jointFail (plainFam k) univ).card ≠ (jointFail (parityFam k) univ).card := by sorry
