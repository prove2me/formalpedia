-- Prove2me | Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
-- name    : MachineLearning_BonferroniMarginals_HigherOrderNecessity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:37:37.528046+00:00
-- url     : https://prove2.me/theorems/48cb2903-a268-4db7-883a-52d435caf4da
-- title:
--   Aether Catalog definitions — MachineLearning_BonferroniMarginals_HigherOrderNecessity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BonferroniMarginals.HigherOrderNecessity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean by skeleton subtraction
import Mathlib
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

namespace BonferroniMarginals

open Finset

/-! ## Joint marginals of arbitrary order -/

/-- The joint event `⋂_{i ∈ T} A i`, computed inside a finite ambient type.
For `T = ∅` this is the whole space.  `(jointFail A T).card` is the marginal of
order `|T|` of the family `A`. -/
def jointFail {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (A : ι → Finset Ω) (T : Finset ι) : Finset Ω :=
  univ.filter (fun x => ∀ i ∈ T, x ∈ A i)

/-! ## Counting subsets with a prescribed size parity -/


/-! ## Supersets of a fixed set -/

variable {k : ℕ}




/-! ## The two families -/

/-- One copy of every subset containing `i`. -/
def plainFam (k : ℕ) (i : Fin k) : Finset (Finset (Fin k) × Bool) :=
  univ.filter (fun p => i ∈ p.1 ∧ p.2 = false)

/-- Two copies of every subset containing `i` whose size has the same parity as `k`. -/
def parityFam (k : ℕ) (i : Fin k) : Finset (Finset (Fin k) × Bool) :=
  univ.filter (fun p => i ∈ p.1 ∧ (p.1.card + k) % 2 = 0)





/-! ## The unions differ -/




/-! ## The main theorem -/



end BonferroniMarginals


