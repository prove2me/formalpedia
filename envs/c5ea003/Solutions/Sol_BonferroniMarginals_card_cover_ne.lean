-- Prove2me | solution 1 for BonferroniMarginals.card_cover_ne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:51.182491+00:00
-- url     : https://prove2.me/submissions/87f800fb-d0ce-4bdf-8fde-c161ca71cb9c

-- Sol generated from MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_MarginalIndeterminacy
import Theorems.Thm_BonferroniMarginals_mem_cover

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

lemma cover_plain :
    cover (univ : Finset (Fin k)) (plainFam k)
      = ((univ : Finset (Finset (Fin k))).filter (fun S => S.Nonempty))
          ×ˢ ({false} : Finset Bool) := by
  ext p
  simp only [mem_cover, plainFam, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Finset.mem_singleton]
  aesop

lemma cover_parity :
    cover (univ : Finset (Fin k)) (parityFam k)
      = ((univ : Finset (Finset (Fin k))).filter
          (fun S => S.Nonempty ∧ (S.card + k) % 2 = 0)) ×ˢ (univ : Finset Bool) := by
  ext p
  simp only [mem_cover, parityFam, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, and_true]
  aesop


/-! ## The main theorem -/




open BonferroniMarginals in
theorem solution(hk : 0 < k) :
    (cover (univ : Finset (Fin k)) (plainFam k)).card
      ≠ (cover (univ : Finset (Fin k)) (parityFam k)).card := by
  classical
  rw [cover_plain, cover_parity, Finset.card_product, Finset.card_product]
  have hplain : ((univ : Finset (Finset (Fin k))).filter (fun S => S.Nonempty)).card
      = 2 ^ k - 1 := by
    have hcompl : ((univ : Finset (Finset (Fin k))).filter (fun S => ¬ S.Nonempty)).card = 1 := by
      have : ((univ : Finset (Finset (Fin k))).filter (fun S => ¬ S.Nonempty))
          = {(∅ : Finset (Fin k))} := by
        ext S
        simp [Finset.not_nonempty_iff_eq_empty]
      rw [this, Finset.card_singleton]
    have htot := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Finset (Fin k)))) (p := fun S => S.Nonempty)
    rw [hcompl] at htot
    have hcard : (univ : Finset (Finset (Fin k))).card = 2 ^ k := by
      simp [Finset.card_univ, Fintype.card_finset]
    rw [hcard] at htot
    omega
  rw [hplain]
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_bool, mul_one]
  intro hcon
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega
