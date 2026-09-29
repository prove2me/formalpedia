-- Prove2me | solution 1 for BonferroniMarginals.jointFail_card_eq_of_ne_univ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:26:09.63845+00:00
-- url     : https://prove2.me/submissions/16b31304-3425-4bba-ac1e-ab8ca2199ef1

-- Sol generated from MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_MarginalIndeterminacy
import Theorems.Thm_BonferroniMarginals_card_filter_superset
import Theorems.Thm_BonferroniMarginals_card_powerset_filter_parity

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


/-- The number of subsets of `Fin k` containing `T` is `2^(k - |T|)`. -/
lemma card_supersets (T : Finset (Fin k)) :
    ((univ : Finset (Finset (Fin k))).filter (fun S => T ⊆ S)).card = 2 ^ (k - T.card) := by
  classical
  have h := card_filter_superset T (fun _ => True)
  simp only [and_true] at h
  rw [h]
  simp [Finset.card_powerset, Finset.card_compl]

/-- Among the subsets of `Fin k` containing a *proper* subset `T`, exactly half
have any prescribed size parity. -/
lemma card_supersets_parity (T : Finset (Fin k)) (hT : T.card < k) (c : ℕ) :
    ((univ : Finset (Finset (Fin k))).filter
        (fun S => T ⊆ S ∧ (S.card + c) % 2 = 0)).card = 2 ^ (k - T.card - 1) := by
  classical
  have hcompl : (Tᶜ : Finset (Fin k)).card = k - T.card := by
    simp [Finset.card_compl]
  have hne : (Tᶜ : Finset (Fin k)).Nonempty := by
    rw [← Finset.card_pos, hcompl]
    omega
  have h := card_filter_superset T (fun n => (n + c) % 2 = 0)
  rw [h]
  simp only [add_assoc]
  rw [card_powerset_filter_parity _ hne (T.card + c), hcompl]

/-! ## The two families -/



lemma jointFail_plain (T : Finset (Fin k)) (hT : T.Nonempty) :
    jointFail (plainFam k) T
      = ((univ : Finset (Finset (Fin k))).filter (fun S => T ⊆ S)) ×ˢ ({false} : Finset Bool) := by
  ext p
  simp only [jointFail, plainFam, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, Finset.mem_singleton]
  obtain ⟨i0, hi0⟩ := hT
  constructor
  · intro h
    exact ⟨fun x hx => (h x hx).1, (h i0 hi0).2⟩
  · intro h
    exact fun i hi => ⟨h.1 hi, h.2⟩

lemma jointFail_parity (T : Finset (Fin k)) (hT : T.Nonempty) :
    jointFail (parityFam k) T
      = ((univ : Finset (Finset (Fin k))).filter (fun S => T ⊆ S ∧ (S.card + k) % 2 = 0))
          ×ˢ (univ : Finset Bool) := by
  ext p
  simp only [jointFail, parityFam, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, and_true]
  obtain ⟨i0, hi0⟩ := hT
  constructor
  · intro h
    exact ⟨fun x hx => (h x hx).1, (h i0 hi0).2⟩
  · intro h
    exact fun i hi => ⟨h.1 hi, h.2⟩



/-! ## The unions differ -/




/-! ## The main theorem -/




open BonferroniMarginals in
theorem solution(T : Finset (Fin k)) (hT : T ≠ univ) :
    (jointFail (plainFam k) T).card = (jointFail (parityFam k) T).card := by
  classical
  have hlt : T.card < k := by
    have h1 : T ⊂ univ := ⟨Finset.subset_univ T, fun h => hT (Finset.Subset.antisymm (Finset.subset_univ T) h)⟩
    have := Finset.card_lt_card h1
    simpa using this
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [jointFail]
  rw [jointFail_plain T hne, jointFail_parity T hne, Finset.card_product, Finset.card_product,
    card_supersets, card_supersets_parity T hlt k]
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_bool, mul_one]
  have hpow : 2 ^ (k - T.card) = 2 ^ (k - T.card - 1) * 2 := by
    conv_lhs => rw [show k - T.card = (k - T.card - 1) + 1 by omega]
    ring
  rw [hpow]
