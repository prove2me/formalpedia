-- Prove2me | solution 1 for lean_workbook_plus_74403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:33:38.928255+00:00
-- url     : https://prove2.me/submissions/a9dcee6a-c019-4e51-a846-b99ec08fc4cc

import Mathlib

set_option autoImplicit false

noncomputable section

namespace PairProductSexticMinimum

def pairProduct (a b c : ℝ) : ℝ := (a + b) * (b + c) * (c + a)

def energy (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) + 12 * a ^ 2 * b ^ 2 * c ^ 2

def cubicGap (a b c : ℝ) : ℝ := (a + b + c) * (a * b + b * c + c * a) - 11 * a * b * c

def vandermonde (a b c : ℝ) : ℝ := (a - b) * (b - c) * (c - a)

theorem certificate (a b c : ℝ) :
    10 * energy a b c - 3 * pairProduct a b c ^ 2 =
      2 * cubicGap a b c ^ 2 + 5 * vandermonde a b c ^ 2 := by
  unfold energy pairProduct cubicGap vandermonde
  ring

theorem bound (a b c : ℝ) : (3 / 10 : ℝ) * pairProduct a b c ^ 2 ≤ energy a b c := by
  have h := certificate a b c
  nlinarith only [h, sq_nonneg (cubicGap a b c), sq_nonneg (vandermonde a b c)]

theorem equality_iff (a b c : ℝ) :
    energy a b c = (3 / 10 : ℝ) * pairProduct a b c ^ 2 ↔
      cubicGap a b c = 0 ∧ vandermonde a b c = 0 := by
  have h := certificate a b c
  constructor
  · intro he
    have hq : cubicGap a b c ^ 2 = 0 := by
      nlinarith only [h, he, sq_nonneg (cubicGap a b c), sq_nonneg (vandermonde a b c)]
    have hd : vandermonde a b c ^ 2 = 0 := by
      nlinarith only [h, he, sq_nonneg (cubicGap a b c), sq_nonneg (vandermonde a b c)]
    exact ⟨sq_eq_zero_iff.mp hq, sq_eq_zero_iff.mp hd⟩
  · rintro ⟨hq, hd⟩
    rw [hq, hd] at h
    nlinarith only [h]

theorem repeated_coordinate_iff (a b c : ℝ) :
    vandermonde a b c = 0 ↔ a = b ∨ b = c ∨ c = a := by
  simp only [vandermonde, mul_eq_zero, sub_eq_zero]
  tauto

theorem positive_equality_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    energy a b c = (3 / 10 : ℝ) * pairProduct a b c ^ 2 ↔
      (a = b ∧ c ^ 2 - 3 * a * c + a ^ 2 = 0) ∨
      (b = c ∧ a ^ 2 - 3 * b * a + b ^ 2 = 0) ∨
      (c = a ∧ b ^ 2 - 3 * c * b + c ^ 2 = 0) := by
  rw [equality_iff]
  constructor
  · rintro ⟨hq, hd⟩
    rcases (repeated_coordinate_iff a b c).mp hd with he | he | he
    · left
      refine ⟨he, ?_⟩
      subst b
      have hi : cubicGap a a c = 2 * a * (c ^ 2 - 3 * a * c + a ^ 2) := by
        unfold cubicGap
        ring
      rw [hi] at hq
      exact (mul_eq_zero.mp hq).resolve_left (by positivity)
    · right; left
      refine ⟨he, ?_⟩
      subst c
      have hi : cubicGap a b b = 2 * b * (a ^ 2 - 3 * b * a + b ^ 2) := by
        unfold cubicGap
        ring
      rw [hi] at hq
      exact (mul_eq_zero.mp hq).resolve_left (by positivity)
    · right; right
      refine ⟨he, ?_⟩
      subst a
      have hi : cubicGap c b c = 2 * c * (b ^ 2 - 3 * c * b + c ^ 2) := by
        unfold cubicGap
        ring
      rw [hi] at hq
      exact (mul_eq_zero.mp hq).resolve_left (by positivity)
  · rintro (⟨he, hq⟩ | ⟨he, hq⟩ | ⟨he, hq⟩)
    · subst b
      constructor
      · have hi : cubicGap a a c = 2 * a * (c ^ 2 - 3 * a * c + a ^ 2) := by
          unfold cubicGap
          ring
        rw [hi, hq, mul_zero]
      · simp [vandermonde]
    · subst c
      constructor
      · have hi : cubicGap a b b = 2 * b * (a ^ 2 - 3 * b * a + b ^ 2) := by
          unfold cubicGap
          ring
        rw [hi, hq, mul_zero]
      · simp [vandermonde]
    · subst a
      constructor
      · have hi : cubicGap c b c = 2 * c * (b ^ 2 - 3 * c * b + c ^ 2) := by
          unfold cubicGap
          ring
        rw [hi, hq, mul_zero]
      · simp [vandermonde]

theorem ratio_roots (u v : ℝ) :
    v ^ 2 - 3 * u * v + u ^ 2 = 0 ↔
      v = u * ((3 + Real.sqrt 5) / 2) ∨ v = u * ((3 - Real.sqrt 5) / 2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hi : (v - u * ((3 + Real.sqrt 5) / 2)) *
      (v - u * ((3 - Real.sqrt 5) / 2)) = v ^ 2 - 3 * u * v + u ^ 2 := by
    nlinarith only [hs, mul_nonneg (sq_nonneg u) (sq_nonneg (Real.sqrt 5))]
  rw [← hi, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem pairProduct_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < pairProduct a b c := by unfold pairProduct; positivity

theorem golden_model :
    let t : ℝ := (3 + Real.sqrt 5) / 2
    0 < t ∧ energy 1 1 t = (3 / 10 : ℝ) * pairProduct 1 1 t ^ 2 := by
  dsimp
  have ht : (0 : ℝ) < (3 + Real.sqrt 5) / 2 := by positivity
  refine ⟨ht, (positive_equality_iff 1 1 _ (by norm_num) (by norm_num) ht).mpr ?_⟩
  refine Or.inl ⟨rfl, ?_⟩
  apply (ratio_roots 1 _).mpr
  left
  ring

theorem sharp_coefficient (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → k * pairProduct a b c ^ 2 ≤ energy a b c) ↔
      k ≤ 3 / 10 := by
  constructor
  · intro h
    let t : ℝ := (3 + Real.sqrt 5) / 2
    have ht : 0 < t := golden_model.1
    have he : energy 1 1 t = (3 / 10 : ℝ) * pairProduct 1 1 t ^ 2 := golden_model.2
    have hp : 0 < pairProduct 1 1 t ^ 2 := sq_pos_of_pos (pairProduct_pos 1 1 t (by norm_num) (by norm_num) ht)
    have hk := h 1 1 t (by norm_num) (by norm_num) ht
    rw [he] at hk
    exact (mul_le_mul_iff_left₀ hp).mp hk
  · intro hk a b c _ _ _
    exact (mul_le_mul_of_nonneg_right hk (sq_nonneg _)).trans (bound a b c)

theorem pairProduct_scale (s a b c : ℝ) :
    pairProduct (s * a) (s * b) (s * c) = s ^ 3 * pairProduct a b c := by
  unfold pairProduct
  ring

theorem energy_scale (s a b c : ℝ) :
    energy (s * a) (s * b) (s * c) = s ^ 6 * energy a b c := by
  unfold energy
  ring

theorem normalized_bound (p a b c : ℝ) (h : pairProduct a b c = p) :
    (3 / 10 : ℝ) * p ^ 2 ≤ energy a b c := by
  simpa only [h] using bound a b c

theorem normalized_attainment (p : ℝ) (hp : 0 < p) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ pairProduct a b c = p ∧
      energy a b c = (3 / 10 : ℝ) * p ^ 2 := by
  let t : ℝ := (3 + Real.sqrt 5) / 2
  have ht : 0 < t := golden_model.1
  have he : energy 1 1 t = (3 / 10 : ℝ) * pairProduct 1 1 t ^ 2 := golden_model.2
  have hT : 0 < pairProduct 1 1 t := pairProduct_pos 1 1 t (by norm_num) (by norm_num) ht
  have hratio : 0 < p / pairProduct 1 1 t := div_pos hp hT
  let s : ℝ := (p / pairProduct 1 1 t) ^ ((3 : ℝ)⁻¹)
  have hs : 0 < s := Real.rpow_pos_of_pos hratio _
  have hs3 : s ^ 3 = p / pairProduct 1 1 t :=
    Real.rpow_inv_natCast_pow hratio.le (by norm_num : (3 : ℕ) ≠ 0)
  have hnorm : pairProduct (s * 1) (s * 1) (s * t) = p := by
    rw [pairProduct_scale, hs3]
    exact div_mul_cancel₀ _ hT.ne'
  refine ⟨s * 1, s * 1, s * t, by positivity, by positivity, by positivity, hnorm, ?_⟩
  rw [energy_scale, he, ← hnorm, pairProduct_scale]
  ring

theorem normalized_minimum (p : ℝ) (hp : 0 < p) :
    IsLeast {v : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ pairProduct a b c = p ∧
      energy a b c = v} ((3 / 10 : ℝ) * p ^ 2) := by
  refine ⟨normalized_attainment p hp, ?_⟩
  rintro v ⟨a, b, c, _, _, _, hpabc, rfl⟩
  exact normalized_bound p a b c hpabc

theorem source_bound (a b c : ℝ) (h : pairProduct a b c = Real.sqrt 10) :
    3 ≤ energy a b c := by
  have hb := normalized_bound (Real.sqrt 10) a b c h
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)] at hb
  norm_num at hb
  exact hb

theorem source_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : pairProduct a b c = Real.sqrt 10) :
    energy a b c = 3 ↔
      (a = b ∧ c ^ 2 - 3 * a * c + a ^ 2 = 0) ∨
      (b = c ∧ a ^ 2 - 3 * b * a + b ^ 2 = 0) ∨
      (c = a ∧ b ^ 2 - 3 * c * b + c ^ 2 = 0) := by
  have he : (3 / 10 : ℝ) * pairProduct a b c ^ 2 = 3 := by rw [h]; norm_num
  simpa only [he] using positive_equality_iff a b c ha hb hc

theorem source_minimum :
    IsLeast {v : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      pairProduct a b c = Real.sqrt 10 ∧ energy a b c = v} 3 := by
  have h := normalized_minimum (Real.sqrt 10) (by positivity)
  have he : (3 / 10 : ℝ) * Real.sqrt 10 ^ 2 = 3 := by norm_num
  rw [he] at h
  exact h

end PairProductSexticMinimum

theorem solution (a b c : ℝ) (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (_habc : a * b * c = 1) (h : (a + b) * (b + c) * (c + a) = Real.sqrt 10) :
    (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) + 12 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 3 :=
  PairProductSexticMinimum.source_bound a b c h

#print axioms PairProductSexticMinimum.pairProduct
#print axioms PairProductSexticMinimum.energy
#print axioms PairProductSexticMinimum.cubicGap
#print axioms PairProductSexticMinimum.vandermonde
#print axioms PairProductSexticMinimum.certificate
#print axioms PairProductSexticMinimum.bound
#print axioms PairProductSexticMinimum.equality_iff
#print axioms PairProductSexticMinimum.repeated_coordinate_iff
#print axioms PairProductSexticMinimum.positive_equality_iff
#print axioms PairProductSexticMinimum.ratio_roots
#print axioms PairProductSexticMinimum.pairProduct_pos
#print axioms PairProductSexticMinimum.golden_model
#print axioms PairProductSexticMinimum.sharp_coefficient
#print axioms PairProductSexticMinimum.pairProduct_scale
#print axioms PairProductSexticMinimum.energy_scale
#print axioms PairProductSexticMinimum.normalized_bound
#print axioms PairProductSexticMinimum.normalized_attainment
#print axioms PairProductSexticMinimum.normalized_minimum
#print axioms PairProductSexticMinimum.source_bound
#print axioms PairProductSexticMinimum.source_equality
#print axioms PairProductSexticMinimum.source_minimum
#print axioms solution
