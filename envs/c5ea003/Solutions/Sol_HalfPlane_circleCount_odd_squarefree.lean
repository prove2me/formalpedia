-- Prove2me | solution 1 for HalfPlane.circleCount_odd_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T14:55:40.489342+00:00
-- url     : https://prove2.me/submissions/67b46df8-5d85-484a-9da0-0b93beebb937

import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Definitions.Def_MachineLearning_HalfPlaneSemiprime

namespace HP121

open Finset

/-- The circle `x² + y² = 1` over a ring, as a subtype. -/
abbrev Circ (R : Type*) [CommRing R] := {q : R × R // q.1 ^ 2 + q.2 ^ 2 = 1}

/-- A ring isomorphism `R ≃ A × B` splits the circle. -/
def circEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] (e : R ≃+* A × B) :
    Circ R ≃ Circ A × Circ B where
  toFun q := (⟨((e q.1.1).1, (e q.1.2).1), by
      have h := congrArg (fun r => (e r).1) q.2
      simpa [map_add, map_pow] using h⟩,
    ⟨((e q.1.1).2, (e q.1.2).2), by
      have h := congrArg (fun r => (e r).2) q.2
      simpa [map_add, map_pow] using h⟩)
  invFun ab := ⟨(e.symm (ab.1.1.1, ab.2.1.1), e.symm (ab.1.1.2, ab.2.1.2)), by
      apply e.injective
      rw [map_add, map_pow, map_pow, map_one, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply]
      ext
      · simpa using ab.1.2
      · simpa using ab.2.2⟩
  left_inv q := by
    apply Subtype.ext
    simp
  right_inv ab := by
    ext <;> simp

lemma card_circ_mul {m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n) :
    Fintype.card (Circ (ZMod (m * n))) = Fintype.card (Circ (ZMod m)) * Fintype.card (Circ (ZMod n)) := by
  rw [Fintype.card_congr (circEquiv (ZMod.chineseRemainder h)), Fintype.card_prod]

/-- Bridge: the natural-number circle count is the `ZMod` circle count. -/
lemma circleCount_eq_card (N : ℕ) [NeZero N] :
    HalfPlane.circleCount N = Fintype.card (Circ (ZMod N)) := by
  rw [Fintype.card_subtype]
  unfold HalfPlane.circleCount HalfPlane.circleFinset
  refine Finset.card_nbij' (fun a => ((a.1 : ZMod N), (a.2 : ZMod N)))
    (fun q => (q.1.val, q.2.val)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range] at ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    have := (ZMod.natCast_eq_natCast_iff' (a.1 ^ 2 + a.2 ^ 2) 1 N).mpr ha.2
    push_cast at this
    exact this
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨ZMod.val_lt _, ZMod.val_lt _⟩, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact hq
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range] at ha
    simp [ZMod.val_cast_of_lt ha.1.1, ZMod.val_cast_of_lt ha.1.2]
  · intro q _
    simp

lemma circleCount_one : HalfPlane.circleCount 1 = 1 := by decide

lemma circleCount_mul {m n : ℕ} (h : Nat.Coprime m n) :
    HalfPlane.circleCount (m * n) = HalfPlane.circleCount m * HalfPlane.circleCount n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h
    subst h
    simp [circleCount_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    subst h
    simp [circleCount_one]
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  rw [circleCount_eq_card, circleCount_eq_card, circleCount_eq_card, card_circ_mul h]

section Prime

/-- Stereographic facts over any field of characteristic not two. -/
lemma stereo_x_ne {F : Type*} [Field F] {x y : F} (hc : x ^ 2 + y ^ 2 = 1)
    (hne : (x, y) ≠ ((-1 : F), (0 : F))) : x + 1 ≠ 0 := by
  intro hx
  apply hne
  have hy2 : y ^ 2 = 0 := by linear_combination hc + (1 - x) * hx
  have hy : y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy2
  have hx' : x = -1 := by linear_combination hx
  rw [hx', hy]

lemma stereo_sq {F : Type*} [Field F] {x y : F} (hc : x ^ 2 + y ^ 2 = 1) (hx : x + 1 ≠ 0) :
    (y / (x + 1)) ^ 2 = (1 - x) / (x + 1) := by
  rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hx) hx]
  linear_combination (x + 1) * hc

lemma stereo_den {F : Type*} [Field F] {x y : F} (hc : x ^ 2 + y ^ 2 = 1) (hx : x + 1 ≠ 0) :
    1 + (y / (x + 1)) ^ 2 = 2 / (x + 1) := by
  rw [stereo_sq hc hx]
  field_simp
  ring

lemma stereo_left {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {x y : F} (hc : x ^ 2 + y ^ 2 = 1)
    (hx : x + 1 ≠ 0) :
    ((1 - (y / (x + 1)) ^ 2) / (1 + (y / (x + 1)) ^ 2), 2 * (y / (x + 1)) / (1 + (y / (x + 1)) ^ 2))
      = (x, y) := by
  have e1 : 1 - (y / (x + 1)) ^ 2 = 2 * x / (x + 1) := by
    rw [stereo_sq hc hx]
    field_simp
    ring
  have e3 : 2 * (y / (x + 1)) = 2 * y / (x + 1) := by ring
  rw [stereo_den hc hx, e1, e3, div_div_div_cancel_right₀ hx, div_div_div_cancel_right₀ hx,
    mul_div_cancel_left₀ _ h2, mul_div_cancel_left₀ _ h2]

lemma stereo_right {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {t : F} (ht : ¬ (1 + t ^ 2 = 0)) :
    (2 * t / (1 + t ^ 2)) / ((1 - t ^ 2) / (1 + t ^ 2) + 1) = t := by
  have e : (1 - t ^ 2) / (1 + t ^ 2) + 1 = 2 / (1 + t ^ 2) := by
    field_simp
    ring
  rw [e, div_div_div_cancel_right₀ ht, mul_div_cancel_left₀ _ h2]

lemma stereo_on {F : Type*} [Field F] {t : F} (ht : ¬ (1 + t ^ 2 = 0)) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  field_simp
  ring

lemma stereo_ne {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {t : F} (ht : ¬ (1 + t ^ 2 = 0)) :
    ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)) ≠ ((-1 : F), (0 : F)) := by
  intro h
  have h1 := congrArg Prod.fst h
  simp only at h1
  rw [div_eq_iff ht] at h1
  exact h2 (by linear_combination h1)

lemma stereo_card {F : Type*} [Field F] [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0) :
    (Finset.univ.filter (fun q : F × F => q.1 ^ 2 + q.2 ^ 2 = 1)).card
      = (Finset.univ.filter (fun t : F => ¬ (1 + t ^ 2 = 0))).card + 1 := by
  have hmem : ((-1 : F), (0 : F)) ∈ Finset.univ.filter (fun q : F × F => q.1 ^ 2 + q.2 ^ 2 = 1) := by
    simp
  rw [← Finset.card_erase_add_one hmem]
  congr 1
  refine Finset.card_nbij' (fun q => q.2 / (q.1 + 1))
    (fun t => ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff] at hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    have hx := stereo_x_ne hq.1 hq.2
    rw [stereo_den hq.1 hx]
    exact div_ne_zero h2 hx
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨stereo_on ht, stereo_ne h2 ht⟩
  · intro q hq
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff] at hq
    have hx := stereo_x_ne hq.1 hq.2
    exact stereo_left h2 hq.1 hx
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
    exact stereo_right h2 ht

variable {p : ℕ} [Fact p.Prime]

lemma two_ne (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)

lemma card_roots (hp2 : p ≠ 2) :
    (Finset.univ.filter (fun t : ZMod p => 1 + t ^ 2 = 0)).card = if p % 4 = 1 then 2 else 0 := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  by_cases h4 : p % 4 = 1
  · rw [if_pos h4]
    obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    have hne : r ≠ -r := by
      intro h
      have h2r : (2 : ZMod p) * r = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2r with h' | h'
      · exact two_ne hp2 h'
      · exact hr0 h'
    have hset : Finset.univ.filter (fun t : ZMod p => 1 + t ^ 2 = 0) = {r, -r} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro ht
        have hm : (t - r) * (t + r) = 0 := by linear_combination ht + hr
        rcases mul_eq_zero.mp hm with h | h
        · left
          linear_combination h
        · right
          linear_combination h
      · rintro (rfl | rfl)
        · linear_combination -hr
        · linear_combination -hr
    rw [hset, Finset.card_pair hne]
  · rw [if_neg h4]
    have h3 : p % 4 = 3 := by omega
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    have hsq : IsSquare (-1 : ZMod p) := ⟨t, by linear_combination -ht⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) h3

lemma circleCount_prime (hp2 : p ≠ 2) :
    HalfPlane.circleCount p = if p % 4 = 1 then p - 1 else p + 1 := by
  rw [circleCount_eq_card, Fintype.card_subtype, stereo_card (two_ne hp2)]
  have hT := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (ZMod p)))
    (fun t : ZMod p => 1 + t ^ 2 = 0)
  rw [Finset.card_univ, ZMod.card, card_roots hp2] at hT
  split_ifs at hT ⊢ <;> omega

end Prime

end HP121

set_option maxHeartbeats 4000000 in
open Finset HalfPlane in
theorem solution {N : ℕ} (hodd : ¬ 2 ∣ N) (hsq : Squarefree N) :
    circleCount N = ∏ p ∈ N.primeFactors, (if p % 4 = 1 then p - 1 else p + 1) := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hsq
  classical
  have hfac := Nat.multiplicative_factorization circleCount
    (fun x y h => HP121.circleCount_mul h) HP121.circleCount_one hN
  rw [hfac, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd hpdvd
  haveI : Fact p.Prime := ⟨hpp⟩
  have hk1 : 1 ≤ N.factorization p := hpp.factorization_pos_of_dvd hN hpdvd
  have hk : N.factorization p = 1 :=
    le_antisymm ((Nat.squarefree_iff_factorization_le_one hN).mp hsq p) hk1
  rw [hk, pow_one, HP121.circleCount_prime hp2]
