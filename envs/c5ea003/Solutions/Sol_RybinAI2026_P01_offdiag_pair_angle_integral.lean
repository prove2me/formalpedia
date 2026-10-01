-- Prove2me | solution 1 for RybinAI2026.P01.offdiag_pair_angle_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T10:58:52.978693+00:00
-- url     : https://prove2.me/submissions/cb119697-648d-46ce-ad01-c89064e38098

import Mathlib
import Theorems.Thm_RybinAI2026_P01_offdiag_denominator_pairing

open Set RybinAI2026.P01

noncomputable section

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 < a * b) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
        |Real.cos θ| / (a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2)
        + |Real.cos θ| / (a * Real.cos θ ^ 2 - 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2))
      = 2 * ∫ s in (0 : ℝ)..1,
          (a + (b - a) * s ^ 2) /
            ((a + (b - a) * s ^ 2) ^ 2 - 4 * c ^ 2 * s ^ 2 * (1 - s ^ 2)) := by
  let A : ℝ → ℝ := fun s => a + (b - a) * s ^ 2
  let D : ℝ → ℝ := fun s => A s ^ 2 - 4 * c ^ 2 * s ^ 2 * (1 - s ^ 2)
  let g : ℝ → ℝ := fun s => (A s + 2 * c * s * Real.sqrt (1 - s ^ 2))⁻¹
  have hpt (θ : ℝ) (hθ : θ ∈ uIcc (-(Real.pi / 2)) (Real.pi / 2)) :
      |Real.cos θ| / (a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2)
        = g (Real.sin θ) * Real.cos θ := by
    have hmem : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 2)] using hθ
    have hc0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have hsq : Real.sqrt (1 - Real.sin θ ^ 2) = Real.cos θ :=
      (Real.cos_eq_sqrt_one_sub_sin_sq (by linarith [hmem.1]) (by linarith [hmem.2])).symm
    have hcos : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
      have h := Real.sin_sq_add_cos_sq θ
      linarith
    have hkey : g (Real.sin θ)
        = (a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2)⁻¹ := by
      have hd : A (Real.sin θ) + 2 * c * Real.sin θ * Real.sqrt (1 - Real.sin θ ^ 2)
          = a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2 := by
        simp only [A]
        rw [hsq, ← hcos]
        ring
      dsimp only [g]
      rw [hd]
    rw [hkey, abs_of_nonneg hc0, div_eq_mul_inv]
    ring
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos)
      (g := fun s => g s + g (-s)) Real.continuous_sin.continuousOn
      (fun θ _ => Real.hasDerivAt_sin θ)
      (fun θ hθ => by
        have hθ' : (0 : ℝ) < θ ∧ θ < Real.pi / 2 := by
          simpa [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
            max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  have hGsub : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (|Real.cos θ| / (a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2)
          + |Real.cos θ| / (a * Real.cos θ ^ 2 - 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2)))
      = ∫ s in (0 : ℝ)..1, (g s + g (-s)) := by
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only
    have hθm : θ ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
    have hb1 : θ ∈ uIcc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 2)]
      exact ⟨by linarith [hθm.1, Real.pi_pos], hθm.2⟩
    have hb2 : -θ ∈ uIcc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 2)]
      exact ⟨by linarith [hθm.2], by linarith [hθm.1, Real.pi_pos]⟩
    have h2 : |Real.cos θ| / (a * Real.cos θ ^ 2 - 2 * c * Real.cos θ * Real.sin θ
          + b * Real.sin θ ^ 2) = g (-Real.sin θ) * Real.cos θ := by
      have h := hpt (-θ) hb2
      rw [Real.cos_neg, Real.sin_neg] at h
      rw [show a * Real.cos θ ^ 2 + 2 * c * Real.cos θ * -Real.sin θ + b * (-Real.sin θ) ^ 2
          = a * Real.cos θ ^ 2 - 2 * c * Real.cos θ * Real.sin θ + b * Real.sin θ ^ 2 by ring] at h
      exact h
    rw [hpt θ hb1, h2]
    simp only [Function.comp_apply]
    ring
  have hpairInt : (∫ s in (0 : ℝ)..1, (g s + g (-s))) = ∫ s in (0 : ℝ)..1, (2 * (A s / D s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    have hpair := RybinAI2026.P01.offdiag_denominator_pairing a b c ha hb hc s hs'
    have hgs : g s = (a + (b - a) * s ^ 2 + 2 * c * s * Real.sqrt (1 - s ^ 2))⁻¹ := by
      dsimp only [g, A]
    have hgn : g (-s) = (a + (b - a) * s ^ 2 - 2 * c * s * Real.sqrt (1 - s ^ 2))⁻¹ := by
      have hd : a + (b - a) * (-s) ^ 2 + 2 * c * (-s) * Real.sqrt (1 - (-s) ^ 2)
          = a + (b - a) * s ^ 2 - 2 * c * s * Real.sqrt (1 - s ^ 2) := by
        rw [neg_sq]
        ring
      dsimp only [g, A]
      rw [hd]
    rw [hgs, hgn, hpair]
    dsimp only [A, D]
    ring
  rw [hGsub, hpairInt, intervalIntegral.integral_const_mul] <;> rfl

end
