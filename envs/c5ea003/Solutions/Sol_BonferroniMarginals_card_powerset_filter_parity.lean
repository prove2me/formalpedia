-- Prove2me | solution 1 for BonferroniMarginals.card_powerset_filter_parity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:54.101439+00:00
-- url     : https://prove2.me/submissions/1da5082e-4d40-495c-be84-8517bc072ff7

-- Sol generated from MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean
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







/-! ## The unions differ -/




/-! ## The main theorem -/




open BonferroniMarginals in
theorem solution{α : Type*} [DecidableEq α] (C : Finset α)
    (hC : C.Nonempty) (c : ℕ) :
    (C.powerset.filter (fun U => (U.card + c) % 2 = 0)).card = 2 ^ (C.card - 1) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := C.powerset)
    (p := fun U : Finset α => (U.card + c) % 2 = 0)
  rw [Finset.card_powerset] at hsplit
  -- the alternating sum vanishes, so the two halves have equal size
  have halt : ∑ U ∈ C.powerset, ((-1 : ℤ)) ^ U.card = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hC
  have hsum : ∑ U ∈ C.powerset, ((-1 : ℤ)) ^ U.card
      = (-1 : ℤ) ^ c * (((C.powerset.filter (fun U : Finset α => (U.card + c) % 2 = 0)).card : ℤ)
          - ((C.powerset.filter (fun U : Finset α => ¬ ((U.card + c) % 2 = 0))).card : ℤ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not C.powerset
      (fun U : Finset α => (U.card + c) % 2 = 0)]
    have h1 : ∀ U ∈ C.powerset.filter (fun U : Finset α => (U.card + c) % 2 = 0),
        ((-1 : ℤ)) ^ U.card = (-1 : ℤ) ^ c := by
      intro U hU
      have hUP : (U.card + c) % 2 = 0 := (Finset.mem_filter.mp hU).2
      have hmod : U.card % 2 = c % 2 := by omega
      rw [neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two]
    have h2 : ∀ U ∈ C.powerset.filter (fun U : Finset α => ¬ ((U.card + c) % 2 = 0)),
        ((-1 : ℤ)) ^ U.card = -((-1 : ℤ) ^ c) := by
      intro U hU
      have hUP : ¬ ((U.card + c) % 2 = 0) := (Finset.mem_filter.mp hU).2
      have hmod : U.card % 2 = (c + 1) % 2 := by omega
      rw [neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two, pow_succ]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [halt] at hsum
  have hne : ((-1 : ℤ)) ^ c ≠ 0 := by positivity
  have hdiff : ((C.powerset.filter (fun U : Finset α => (U.card + c) % 2 = 0)).card : ℤ)
      = ((C.powerset.filter (fun U : Finset α => ¬ ((U.card + c) % 2 = 0))).card : ℤ) := by
    rcases mul_eq_zero.mp hsum.symm with h | h
    · exact absurd h hne
    · linarith
  have heq : (C.powerset.filter (fun U : Finset α => (U.card + c) % 2 = 0)).card
      = (C.powerset.filter (fun U : Finset α => ¬ ((U.card + c) % 2 = 0))).card := by
    exact_mod_cast hdiff
  have hC1 : 1 ≤ C.card := Finset.card_pos.mpr hC
  have hpow : 2 ^ C.card = 2 * 2 ^ (C.card - 1) := by
    conv_lhs => rw [show C.card = (C.card - 1) + 1 by omega]
    ring
  omega
