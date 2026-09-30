-- Prove2me | solution 1 for lean_workbook_plus_16613
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:23:50.565399+00:00
-- url     : https://prove2.me/submissions/0a2a43a7-aca7-46b4-8439-538c2644a769

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem joukowski_norm_identity (z : ℂ) (hz : z ≠ 0) :
    ‖z + z⁻¹‖ ^ 2 * Complex.normSq z =
      (Complex.normSq z - 1) ^ 2 + 4 * z.re ^ 2 := by
  have hq : Complex.normSq z ≠ 0 := mt Complex.normSq_eq_zero.mp hz
  have hc : ‖z + z⁻¹‖ ^ 2 =
      (z.re + z.re / Complex.normSq z) ^ 2 +
        (z.im - z.im / Complex.normSq z) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.inv_re, Complex.inv_im]
    ring
  rw [hc]
  field_simp [hq]
  simp only [Complex.normSq_apply]
  ring

theorem joukowski_modulus_range (a r : ℝ) :
    (∃ z : ℂ, z ≠ 0 ∧ ‖z‖ = r ∧ ‖z + 1 / z‖ = a) ↔
      0 < r ∧ |r - 1 / r| ≤ a ∧ a ≤ r + 1 / r := by
  constructor
  · rintro ⟨z, hz, hzr, hza⟩
    refine ⟨hzr ▸ norm_pos_iff.mpr hz, ?_, ?_⟩
    · simpa only [norm_neg, norm_div, norm_one, hzr, sub_neg_eq_add, hza] using
        abs_norm_sub_norm_le z (-(1 / z))
    · simpa only [norm_div, norm_one, hzr, hza] using norm_add_le z (1 / z)
  · rintro ⟨hr, hlo, hhi⟩
    have ha : 0 ≤ a := le_trans (abs_nonneg _) hlo
    have hspan : (r + 1 / r) ^ 2 - (r - 1 / r) ^ 2 = 4 := by
      field_simp [hr.ne']
      ring
    have hu0 : 0 ≤ (a ^ 2 - (r - 1 / r) ^ 2) / 4 := by
      nlinarith [sq_abs (r - 1 / r), abs_nonneg (r - 1 / r)]
    have hu1 : (a ^ 2 - (r - 1 / r) ^ 2) / 4 ≤ 1 := by
      have hp : 0 < r + 1 / r := add_pos hr (one_div_pos.mpr hr)
      nlinarith
    let u := (a ^ 2 - (r - 1 / r) ^ 2) / 4
    have hs : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0
    have ht : Real.sqrt (1 - u) ^ 2 = 1 - u :=
      Real.sq_sqrt (sub_nonneg.mpr hu1)
    let z : ℂ := ((r * Real.sqrt u : ℝ) : ℂ) +
      ((r * Real.sqrt (1 - u) : ℝ) : ℂ) * Complex.I
    have hzq : Complex.normSq z = r ^ 2 := by
      dsimp [z]
      rw [Complex.normSq_add_mul_I]
      calc
        (r * Real.sqrt u) ^ 2 + (r * Real.sqrt (1 - u)) ^ 2 =
            r ^ 2 * (Real.sqrt u ^ 2 + Real.sqrt (1 - u) ^ 2) := by ring
        _ = r ^ 2 := by rw [hs, ht]; ring
    have hzr : ‖z‖ = r := by
      rw [Complex.normSq_eq_norm_sq] at hzq
      nlinarith [norm_nonneg z]
    have hz : z ≠ 0 := norm_pos_iff.mp (hzr ▸ hr)
    have hreal : z.re = r * Real.sqrt u := by simp [z]
    have halg : (r ^ 2 - 1) ^ 2 + 4 * r ^ 2 * u = a ^ 2 * r ^ 2 := by
      dsimp [u]
      field_simp [hr.ne']
      ring
    have hj : ‖z + z⁻¹‖ ^ 2 * r ^ 2 = a ^ 2 * r ^ 2 := by
      calc
        ‖z + z⁻¹‖ ^ 2 * r ^ 2 = (r ^ 2 - 1) ^ 2 + 4 * z.re ^ 2 := by
          simpa only [hzq] using joukowski_norm_identity z hz
        _ = (r ^ 2 - 1) ^ 2 + 4 * r ^ 2 * u := by
          rw [hreal, mul_pow, hs]
          ring
        _ = a ^ 2 * r ^ 2 := halg
    have hj2 : ‖z + z⁻¹‖ ^ 2 = a ^ 2 :=
      mul_right_cancel₀ (pow_ne_zero 2 hr.ne') hj
    have hja : ‖z + z⁻¹‖ = a := by nlinarith [norm_nonneg (z + z⁻¹)]
    exact ⟨z, hz, hzr, by simpa only [one_div] using hja⟩

theorem solution (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : z ≠ 0)
    (h : ‖z + 1 / z‖ = a) : ‖z‖ ∈ Set.Ioi 0 ∪ Set.Ioi a := by
  have hrange := (joukowski_modulus_range a ‖z‖).mp ⟨z, hz, rfl, h⟩
  exact Or.inl hrange.1

#print axioms joukowski_norm_identity
#print axioms joukowski_modulus_range
#print axioms solution
