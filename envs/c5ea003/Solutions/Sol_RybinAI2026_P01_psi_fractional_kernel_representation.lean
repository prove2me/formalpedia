-- Prove2me | solution 1 for RybinAI2026.P01.psi_fractional_kernel_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T02:51:54.979092+00:00
-- url     : https://prove2.me/submissions/f2566212-1406-43c7-92c7-ad7a0bd8d189

import Mathlib

open MeasureTheory

theorem solution (u : ℝ) (hu : 0 < u) :
    ∫ s in (0 : ℝ)..1, (1 + (u ^ 2 - 1) * s ^ 2)⁻¹ =
      ∫ r in (0 : ℝ)..1,
        (2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2))⁻¹ := by
  let den : ℝ → ℝ := fun r => u + (1 - u) * r
  let phi : ℝ → ℝ := fun r => r / den r
  let phi' : ℝ → ℝ := fun r => u / (den r) ^ 2
  let kernel : ℝ → ℝ := fun s => (1 + (u ^ 2 - 1) * s ^ 2)⁻¹
  let q : ℝ → ℝ := fun r => 2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2)
  have hden (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : 0 < den r := by
    by_cases h : u ≤ 1
    · have hm := mul_nonneg (sub_nonneg.mpr h) hr.1
      dsimp [den]
      nlinarith
    · have h1 : 1 < u := lt_of_not_ge h
      have hm := mul_nonneg (sub_nonneg.mpr h1.le) (sub_nonneg.mpr hr.2)
      dsimp [den]
      nlinarith
  have hdenCont : ContinuousOn den (Set.uIcc (0 : ℝ) 1) := by
    dsimp [den]
    fun_prop
  have hphiCont : ContinuousOn phi (Set.uIcc (0 : ℝ) 1) := by
    dsimp [phi]
    refine continuousOn_id.div hdenCont ?_
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hr
    exact ne_of_gt (hden r hr')
  have hdenDeriv (r : ℝ) : HasDerivAt den (1 - u) r := by
    dsimp [den]
    convert ((hasDerivAt_id' r).const_mul (1 - u)).const_add u using 1 <;> ring
  have hphiDeriv (r : ℝ)
      (hr : r ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) :
      HasDerivAt phi (phi' r) r := by
    have hr' : r ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [min_eq_left zero_le_one, max_eq_right zero_le_one] using hr
    have hrcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr'.1.le, hr'.2.le⟩
    have hd := hden r hrcc
    have hquot := (hasDerivAt_id' r).div (hdenDeriv r) (ne_of_gt hd)
    convert hquot using 1
    dsimp [phi, phi', den]
    field_simp [ne_of_gt hd]
    <;> ring
  have hphi'Nonneg (r : ℝ)
      (_hr : r ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) :
      0 ≤ phi' r := by
    dsimp [phi']
    exact div_nonneg hu.le (sq_nonneg (den r))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := phi) (f' := phi') (g := kernel)
    hphiCont hphiDeriv hphi'Nonneg
  have hzero : phi 0 = 0 := by simp [phi, den]
  have hone : phi 1 = 1 := by
    dsimp [phi, den]
    have hd : u + (1 - u) * 1 = 1 := by ring
    rw [hd]
    norm_num
  rw [hzero, hone] at hsub
  have hpoint (r : ℝ) (hr : r ∈ Set.uIcc (0 : ℝ) 1) :
      kernel (phi r) * phi' r = (q r)⁻¹ := by
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hr
    have hd := hden r hr'
    have hbase : 0 ≤ 2 * r * (1 - r) :=
      mul_nonneg (mul_nonneg (by norm_num) hr'.1)
        (sub_nonneg.mpr hr'.2)
    have hq0 : 0 < r ^ 2 + (1 - r) ^ 2 := by
      nlinarith [sq_nonneg (2 * r - 1)]
    have hq : 0 < q r := by
      dsimp [q]
      exact add_pos_of_nonneg_of_pos hbase (mul_pos hu hq0)
    have hpoly : (den r) ^ 2 + (u ^ 2 - 1) * r ^ 2 = u * q r := by
      dsimp [den, q]
      ring
    have hfrac :
        1 + (u ^ 2 - 1) * (r / den r) ^ 2 =
          ((den r) ^ 2 + (u ^ 2 - 1) * r ^ 2) / (den r) ^ 2 := by
      field_simp [ne_of_gt hd]
    change (1 + (u ^ 2 - 1) * (r / den r) ^ 2)⁻¹ *
      (u / (den r) ^ 2) = (q r)⁻¹
    rw [hfrac, hpoly]
    field_simp [ne_of_gt hu, ne_of_gt hq, ne_of_gt hd]
  calc
    _ = ∫ r in (0 : ℝ)..1, kernel (phi r) * phi' r := by
      simpa [kernel] using hsub.symm
    _ = ∫ r in (0 : ℝ)..1, (q r)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hpoint r (by simpa only [Set.uIcc_of_le zero_le_one] using hr)
