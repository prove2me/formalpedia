-- Prove2me | solution 1 for HalfPlane.circleCount_odd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T14:03:50.893431+00:00
-- url     : https://prove2.me/submissions/982524d1-4cbb-4653-ba75-4909e30f0d87

import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm

namespace HP76

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
  have hT := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
    (fun t : ZMod p => 1 + t ^ 2 = 0)
  rw [Finset.card_univ, ZMod.card, card_roots hp2] at hT
  split_ifs at hT ⊢ <;> omega

end Prime


/-! ### Two-chart count over a ring whose units are detected by a map to a field -/

section Charts

variable {R F : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Field F] [DecidableEq F]

lemma ne_zero_of_mul_one' (f : R →+* F) {a b : R} (h : a * b = 1) : ¬ (f a = 0) := by
  have h' : f a * f b = 1 := by rw [← map_mul, h, map_one]
  exact left_ne_zero_of_mul_eq_one h'

lemma ne_zero_of_mul_one'' (f : R →+* F) {a b : R} (h : a * b = 1) : ¬ (f b = 0) := by
  have h' : f a * f b = 1 := by rw [← map_mul, h, map_one]
  exact right_ne_zero_of_mul_eq_one h'

lemma chart1 (f : R →+* F) (inv : R → R) (hinv : ∀ a, ¬ (f a = 0) → a * inv a = 1)
    (h2 : (2 : F) ≠ 0) :
    (univ.filter (fun q : R × R => q.1 ^ 2 + q.2 ^ 2 = 1 ∧ ¬ (f (q.1 + 1) = 0))).card
      = (univ.filter (fun t : R => ¬ (f (1 + t ^ 2) = 0))).card := by
  have h2R : (2 : R) * inv 2 = 1 := hinv 2 (by rw [map_ofNat]; exact h2)
  refine Finset.card_nbij' (fun q => q.2 * inv (q.1 + 1))
    (fun t => ((1 - t ^ 2) * inv (1 + t ^ 2), 2 * t * inv (1 + t ^ 2))) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
    obtain ⟨hc, hf⟩ := hq
    have hu := hinv _ hf
    have e1 : 1 + (y * inv (x + 1)) ^ 2 = 2 * inv (x + 1) := by
      linear_combination (inv (x + 1)) ^ 2 * hc - (1 - inv (x + 1) + x * inv (x + 1)) * hu
    rw [e1, map_mul, map_ofNat]
    exact mul_ne_zero h2 (ne_zero_of_mul_one'' f hu)
  · intro t ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht ⊢
    have hv := hinv _ ht
    refine ⟨?_, ?_⟩
    · linear_combination ((1 + t ^ 2) * inv (1 + t ^ 2) + 1) * hv
    · have e : (1 - t ^ 2) * inv (1 + t ^ 2) + 1 = 2 * inv (1 + t ^ 2) := by
        linear_combination (-1 : R) * hv
      rw [e, map_mul, map_ofNat]
      exact mul_ne_zero h2 (ne_zero_of_mul_one'' f hv)
  · rintro ⟨x, y⟩ hq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hq
    obtain ⟨hc, hf⟩ := hq
    have hu := hinv _ hf
    simp only [Prod.mk.injEq]
    set u := inv (x + 1) with hu_def
    have e1 : 1 + (y * u) ^ 2 = 2 * u := by
      linear_combination u ^ 2 * hc - (1 - u + x * u) * hu
    have hne : ¬ (f (1 + (y * u) ^ 2) = 0) := by
      rw [e1, map_mul, map_ofNat]
      exact mul_ne_zero h2 (ne_zero_of_mul_one'' f hu)
    have hv := hinv _ hne
    set v := inv (1 + (y * u) ^ 2) with hv_def
    set h := inv (2 : R)
    have ev : v = h * (x + 1) := by
      linear_combination -v * hu + (x + 1) * (-u * v * h2R + h * hv - h * v * e1)
    rw [ev]
    constructor
    · linear_combination x * h2R - 2 * h * hu - h * (x + 1) * e1
    · linear_combination y * u * (x + 1) * h2R + y * hu
  · intro t ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht
    have hv := hinv _ ht
    set v := inv (1 + t ^ 2) with hv_def
    have e : (1 - t ^ 2) * v + 1 = 2 * v := by
      linear_combination (-1 : R) * hv
    have hne : ¬ (f ((1 - t ^ 2) * v + 1) = 0) := by
      rw [e, map_mul, map_ofNat]
      exact mul_ne_zero h2 (ne_zero_of_mul_one'' f hv)
    have hu := hinv _ hne
    simp only
    linear_combination t * hu - t * inv ((1 - t ^ 2) * v + 1) * e

lemma chart2 (f : R →+* F) (inv : R → R) (hinv : ∀ a, ¬ (f a = 0) → a * inv a = 1)
    (h2 : (2 : F) ≠ 0) :
    (univ.filter (fun q : R × R => q.1 ^ 2 + q.2 ^ 2 = 1 ∧ ¬ ¬ (f (q.1 + 1) = 0))).card
      = (univ.filter (fun s : R => f s = 0)).card := by
  have h2R : (2 : R) * inv 2 = 1 := hinv 2 (by rw [map_ofNat]; exact h2)
  refine Finset.card_nbij' (fun q => q.2 * inv (q.1 - 1))
    (fun s => ((s ^ 2 - 1) * inv (1 + s ^ 2), -2 * s * inv (1 + s ^ 2))) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, not_not] at hq ⊢
    obtain ⟨hc, hf⟩ := hq
    have hfc : f x ^ 2 + f y ^ 2 = 1 := by
      have := congrArg f hc
      simpa [map_add, map_pow] using this
    have hx : f x = -1 := by
      rw [map_add, map_one] at hf
      linear_combination hf
    have hy2 : f y ^ 2 = 0 := by
      rw [hx] at hfc
      linear_combination hfc
    have hy : f y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy2
    rw [map_mul, hy, zero_mul]
  · intro s hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, not_not] at hs ⊢
    have hne : ¬ (f (1 + s ^ 2) = 0) := by
      rw [map_add, map_one, map_pow, hs]
      norm_num
    have hv := hinv _ hne
    refine ⟨?_, ?_⟩
    · linear_combination ((1 + s ^ 2) * inv (1 + s ^ 2) + 1) * hv
    · have e : (s ^ 2 - 1) * inv (1 + s ^ 2) + 1 = 2 * s ^ 2 * inv (1 + s ^ 2) := by
        linear_combination (-1 : R) * hv
      rw [e, map_mul, map_mul, map_pow, hs]
      ring
  · rintro ⟨x, y⟩ hq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, not_not] at hq
    obtain ⟨hc, hf⟩ := hq
    have hne1 : ¬ (f (x - 1) = 0) := by
      have : f (x - 1) = f (x + 1) - 2 := by
        rw [map_sub, map_add, map_one]
        ring
      rw [this, hf]
      intro h
      apply h2
      linear_combination -h
    have hw := hinv _ hne1
    simp only [Prod.mk.injEq]
    set w := inv (x - 1) with hw_def
    have e1 : 1 + (y * w) ^ 2 = -2 * w := by
      linear_combination w ^ 2 * hc - (1 + (x + 1) * w) * hw
    have hne : ¬ (f (1 + (y * w) ^ 2) = 0) := by
      rw [e1, map_mul, map_neg, map_ofNat]
      exact mul_ne_zero (neg_ne_zero.mpr h2) (ne_zero_of_mul_one'' f hw)
    have hv := hinv _ hne
    set v := inv (1 + (y * w) ^ 2) with hv_def
    set h := inv (2 : R)
    have ev : v = -h * (x - 1) := by
      linear_combination (x - 1) * (-w * v * h2R - h * hv + h * v * e1) - v * hw
    rw [ev]
    constructor
    · linear_combination -h * (x - 1) * e1 + 2 * h * hw + x * h2R
    · linear_combination 2 * h * y * hw + y * h2R
  · intro s hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hs
    have hne : ¬ (f (1 + s ^ 2) = 0) := by
      rw [map_add, map_one, map_pow, hs]
      norm_num
    have hv := hinv _ hne
    set v := inv (1 + s ^ 2) with hv_def
    have e : (s ^ 2 - 1) * v - 1 = -2 * v := by
      linear_combination hv
    have hne1 : ¬ (f ((s ^ 2 - 1) * v - 1) = 0) := by
      rw [e, map_mul, map_neg, map_ofNat]
      exact mul_ne_zero (neg_ne_zero.mpr h2) (ne_zero_of_mul_one'' f hv)
    have hw := hinv _ hne1
    simp only
    linear_combination s * hw - s * inv ((s ^ 2 - 1) * v - 1) * e

lemma circ_two_charts (f : R →+* F) (inv : R → R) (hinv : ∀ a, ¬ (f a = 0) → a * inv a = 1)
    (h2 : (2 : F) ≠ 0) :
    (univ.filter (fun q : R × R => q.1 ^ 2 + q.2 ^ 2 = 1)).card
      = (univ.filter (fun t : R => ¬ (f (1 + t ^ 2) = 0))).card
        + (univ.filter (fun s : R => f s = 0)).card := by
  rw [← chart1 f inv hinv h2, ← chart2 f inv hinv h2]
  have := Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun q : R × R => q.1 ^ 2 + q.2 ^ 2 = 1)) (fun q => ¬ (f (q.1 + 1) = 0))
  rw [Finset.filter_filter, Finset.filter_filter] at this
  exact this.symm

/-- Fibre count for a surjective ring map. -/
lemma fiber_count (f : R →+* F) [Fintype F] (hs : Function.Surjective f) (P : F → Prop)
    [DecidablePred P] :
    (univ.filter (fun t : R => P (f t))).card
      = (univ.filter (fun t : R => f t = 0)).card * (univ.filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := univ.filter P)
    (by intro x hx; simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢; exact hx)]
  rw [Finset.sum_const_nat (m := (univ.filter (fun t : R => f t = 0)).card), mul_comm]
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb
  obtain ⟨t0, rfl⟩ := hs b
  refine Finset.card_nbij' (fun a => a - t0) (fun a => a + t0) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
    rw [map_sub, ha.2, sub_self]
  · intro a ha
    simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
    rw [map_add, ha, zero_add]
    exact ⟨hb, rfl⟩
  · intro a _
    simp
  · intro a _
    simp

end Charts

section PrimePow

variable {p : ℕ} [hp : Fact p.Prime]

lemma unit_detect {k : ℕ} (hk : 0 < k) (a : ZMod (p ^ k)) :
    ¬ (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) a = 0) → a * a⁻¹ = 1 := by
  intro ha
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  apply ZMod.mul_inv_of_unit
  rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hk,
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  rw [← ZMod.natCast_zmod_val a, map_natCast, ZMod.natCast_eq_zero_iff] at ha
  exact ha

lemma cc_prime_pow (hp2 : p ≠ 2) {k : ℕ} (hk : 0 < k) :
    HalfPlane.circleCount (p ^ k) = p ^ (k - 1) * HalfPlane.circleCount p := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set f := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) with hf_def
  have hsurj : Function.Surjective f := ZMod.ringHom_surjective f
  have h2 : (2 : ZMod p) ≠ 0 := two_ne hp2
  have key := circ_two_charts f (fun a => a⁻¹) (unit_detect hk) h2
  have hA : (univ.filter (fun t : ZMod (p ^ k) => ¬ (f (1 + t ^ 2) = 0))).card
      = (univ.filter (fun t : ZMod (p ^ k) => f t = 0)).card
        * (univ.filter (fun s : ZMod p => ¬ (1 + s ^ 2 = 0))).card := by
    rw [← fiber_count f hsurj (fun s : ZMod p => ¬ (1 + s ^ 2 = 0))]
    congr 1
    ext t
    simp only [mem_filter, mem_univ, true_and, map_add, map_one, map_pow]
  have hall := fiber_count f hsurj (fun _ : ZMod p => True)
  rw [Finset.filter_true, Finset.filter_true, Finset.card_univ, Finset.card_univ, ZMod.card,
    ZMod.card] at hall
  set c := (univ.filter (fun t : ZMod (p ^ k) => f t = 0)).card with hc_def
  have hc : c = p ^ (k - 1) := by
    have hpk : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    have hall' : p ^ (k - 1) * p = c * p := by rw [← hpk]; exact hall
    exact (Nat.eq_of_mul_eq_mul_right hp.out.pos hall').symm
  rw [circleCount_eq_card, circleCount_eq_card, Fintype.card_subtype, Fintype.card_subtype,
    key, hA, stereo_card h2, ← hc]
  ring

end PrimePow

end HP76

set_option maxHeartbeats 4000000 in
open HalfPlane Finset in
theorem solution {N : ℕ} (hN : N ≠ 0) (hodd : ¬ 2 ∣ N) :
    circleCount N
      = ∏ p ∈ N.primeFactors,
          p ^ (N.factorization p - 1) * (if p % 4 = 1 then p - 1 else p + 1) := by
  classical
  have hfac := Nat.multiplicative_factorization circleCount
    (fun x y h => HP76.circleCount_mul h) HP76.circleCount_one hN
  rw [hfac, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd hpdvd
  haveI : Fact p.Prime := ⟨hpp⟩
  have hk1 : 0 < N.factorization p := hpp.factorization_pos_of_dvd hN hpdvd
  rw [HP76.cc_prime_pow hp2 hk1, HP76.circleCount_prime hp2]
