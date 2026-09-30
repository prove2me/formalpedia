-- Prove2me | solution 1 for lean_workbook_plus_5490
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:43:48.410516+00:00
-- url     : https://prove2.me/submissions/907fdc38-42f5-41c6-94a1-dcb1222c24f5

import Mathlib

namespace MixedPowerConstraintRange

noncomputable def ratio (a b : ℝ) : ℝ := a ^ 3 / b

theorem gap_identity (a b : ℝ) :
    a ^ 9 - 8 * b ^ 3 = a * (a ^ 4 - 4) ^ 2 + 8 * (a ^ 5 - b ^ 3 - 2 * a) := by
  ring

theorem source_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 2 * a ≤ a ^ 5 - b ^ 3) : 2 * b ≤ a ^ 3 := by
  have hs := mul_nonneg ha.le (sq_nonneg (a ^ 4 - 4))
  have hc : (2 * b) ^ 3 ≤ (a ^ 3) ^ 3 := by
    nlinarith only [gap_identity a b, hs, hab]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp hc

theorem sqrt_two_cube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.sqrt 2 ^ 3 = Real.sqrt 2 * Real.sqrt 2 ^ 2 := by ring
    _ = 2 * Real.sqrt 2 := by rw [hs]; ring

theorem sqrt_two_fifth : Real.sqrt 2 ^ 5 = 4 * Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.sqrt 2 ^ 5 = Real.sqrt 2 * (Real.sqrt 2 ^ 2) ^ 2 := by ring
    _ = 4 * Real.sqrt 2 := by rw [hs]; ring

theorem equality_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 2 * a ≤ a ^ 5 - b ^ 3) :
    a ^ 3 = 2 * b ↔ a = Real.sqrt 2 ∧ b = Real.sqrt 2 := by
  constructor
  · intro he
    have h9 : a ^ 9 = 8 * b ^ 3 := by
      calc
        a ^ 9 = (a ^ 3) ^ 3 := by ring
        _ = (2 * b) ^ 3 := by rw [he]
        _ = 8 * b ^ 3 := by ring
    have hs := mul_nonneg ha.le (sq_nonneg (a ^ 4 - 4))
    have hz : a * (a ^ 4 - 4) ^ 2 = 0 := by
      linarith only [gap_identity a b, h9, hab, hs]
    have hz' := (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
    have h4 : a ^ 4 = 4 := by nlinarith only [hz']
    have h2 : a ^ 2 = 2 :=
      (sq_eq_sq₀ (sq_nonneg a) (by norm_num : (0 : ℝ) ≤ 2)).mp (by nlinarith only [h4])
    have ha' : a = Real.sqrt 2 :=
      (sq_eq_sq₀ ha.le (Real.sqrt_nonneg 2)).mp
        (h2.trans (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm)
    refine ⟨ha', ?_⟩
    rw [ha', sqrt_two_cube] at he
    linarith only [he]
  · rintro ⟨rfl, rfl⟩
    exact sqrt_two_cube

theorem equality_model :
    0 < Real.sqrt 2 ∧ 2 * Real.sqrt 2 ≤ Real.sqrt 2 ^ 5 - Real.sqrt 2 ^ 3 := by
  refine ⟨Real.sqrt_pos.mpr (by norm_num), ?_⟩
  rw [sqrt_two_fifth, sqrt_two_cube]
  linarith

theorem ratio_lower_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 2 * a ≤ a ^ 5 - b ^ 3) : 2 ≤ ratio a b := by
  exact (le_div_iff₀ hb).mpr (source_bound ha hb hab)

theorem ratio_equality {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 2 * a ≤ a ^ 5 - b ^ 3) :
    ratio a b = 2 ↔ a = Real.sqrt 2 ∧ b = Real.sqrt 2 := by
  rw [ratio, div_eq_iff (ne_of_gt hb)]
  exact equality_iff ha hb hab

theorem ratio_attains {z : ℝ} (hz : 2 ≤ z) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 2 * a ≤ a ^ 5 - b ^ 3 ∧ ratio a b = z := by
  have hr := equality_model.1
  have hz0 : 0 < z := by linarith
  let b := 2 * Real.sqrt 2 / z
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : b ≤ Real.sqrt 2 := by
    apply (div_le_iff₀ hz0).mpr
    have hm := mul_nonneg (sub_nonneg.mpr hz) hr.le
    nlinarith only [hm]
  have hb3 := pow_le_pow_left₀ hb.le hbr 3
  have hfeas : 2 * Real.sqrt 2 ≤ Real.sqrt 2 ^ 5 - b ^ 3 := by
    rw [sqrt_two_cube] at hb3
    rw [sqrt_two_fifth]
    linarith only [hb3]
  refine ⟨Real.sqrt 2, b, hr, hb, hfeas, ?_⟩
  unfold ratio
  apply (div_eq_iff (ne_of_gt hb)).mpr
  rw [sqrt_two_cube]
  dsimp [b]
  field_simp

theorem attained_ratio_range :
    {z : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 2 * a ≤ a ^ 5 - b ^ 3 ∧ ratio a b = z} =
      Set.Ici 2 := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ratio_lower_bound ha hb hab
  · exact ratio_attains

theorem least_ratio : IsLeast
    {z : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 2 * a ≤ a ^ 5 - b ^ 3 ∧ ratio a b = z} 2 := by
  rw [attained_ratio_range]
  exact ⟨by simp, fun _ h => h⟩

theorem sharp_coefficient (k : ℝ) :
    (∀ a b : ℝ, 0 < a → 0 < b → 2 * a ≤ a ^ 5 - b ^ 3 → k * b ≤ a ^ 3) ↔ k ≤ 2 := by
  constructor
  · intro h
    have hr := equality_model.1
    have hv := h (Real.sqrt 2) (Real.sqrt 2) hr hr equality_model.2
    rw [sqrt_two_cube] at hv
    exact (mul_le_mul_iff_left₀ hr).mp (by simpa only [mul_comm] using hv)
  · intro hk a b ha hb hab
    exact (mul_le_mul_of_nonneg_right hk hb.le).trans (source_bound ha hb hab)

end MixedPowerConstraintRange

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ^ 5 - b ^ 3 ≥ 2 * a) : a ^ 3 ≥ 2 * b :=
  MixedPowerConstraintRange.source_bound ha hb hab

#print axioms MixedPowerConstraintRange.ratio
#print axioms MixedPowerConstraintRange.gap_identity
#print axioms MixedPowerConstraintRange.source_bound
#print axioms MixedPowerConstraintRange.sqrt_two_cube
#print axioms MixedPowerConstraintRange.sqrt_two_fifth
#print axioms MixedPowerConstraintRange.equality_iff
#print axioms MixedPowerConstraintRange.equality_model
#print axioms MixedPowerConstraintRange.ratio_lower_bound
#print axioms MixedPowerConstraintRange.ratio_equality
#print axioms MixedPowerConstraintRange.ratio_attains
#print axioms MixedPowerConstraintRange.attained_ratio_range
#print axioms MixedPowerConstraintRange.least_ratio
#print axioms MixedPowerConstraintRange.sharp_coefficient
#print axioms solution
