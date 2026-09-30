-- Prove2me | solution 1 for RybinAI2026.P01.psi_fractional_order_properties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T03:48:33.462318+00:00
-- url     : https://prove2.me/submissions/68376418-98c2-4acc-9276-2a5db2714dd1

import Mathlib
import Theorems.Thm_RybinAI2026_P01_psi_fractional_kernel_representation
import Theorems.Thm_RybinAI2026_P01_fractional_kernel_pointwise_order
import Theorems.Thm_RybinAI2026_P01_psi_integral_pos

open MeasureTheory

theorem solution :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    let G : ℝ → ℝ := fun t => Real.sqrt t * ψ t
    (∀ t, 0 < t → 0 < G t) ∧
      MonotoneOn G (Set.Ioi 0) ∧
      AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0) := by
  let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
  let G : ℝ → ℝ := fun t => Real.sqrt t * ψ t
  let Δ : ℝ → ℝ → ℝ := fun u r =>
    2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2)
  change (∀ t, 0 < t → 0 < G t) ∧
    MonotoneOn G (Set.Ioi 0) ∧
    AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0)
  have hDpos (u : ℝ) (hu : 0 < u) (r : ℝ)
      (hr : r ∈ Set.Icc (0 : ℝ) 1) : 0 < Δ u r := by
    have hbase : 0 ≤ 2 * r * (1 - r) :=
      mul_nonneg (mul_nonneg (by norm_num) hr.1) (sub_nonneg.mpr hr.2)
    have hq : 0 < r ^ 2 + (1 - r) ^ 2 := by
      nlinarith [sq_nonneg (2 * r - 1)]
    dsimp [Δ]
    exact add_pos_of_nonneg_of_pos hbase (mul_pos hu hq)
  have hGrep (t : ℝ) (ht : 0 < t) :
      G t = ∫ r in (0 : ℝ)..1, Real.sqrt t / Δ (Real.sqrt t) r := by
    have hu : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hr := RybinAI2026.P01.psi_fractional_kernel_representation
      (Real.sqrt t) hu
    rw [Real.sq_sqrt ht.le] at hr
    change Real.sqrt t * (∫ s in (0 : ℝ)..1,
      (1 + (t - 1) * s ^ 2)⁻¹) = _
    rw [hr]
    change Real.sqrt t * (∫ r in (0 : ℝ)..1, (Δ (Real.sqrt t) r)⁻¹) = _
    calc
      _ = ∫ r in (0 : ℝ)..1, Real.sqrt t * (Δ (Real.sqrt t) r)⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
      _ = ∫ r in (0 : ℝ)..1, Real.sqrt t / Δ (Real.sqrt t) r := by
        apply intervalIntegral.integral_congr
        intro r hr
        simp [div_eq_mul_inv]
  have hHrep (t : ℝ) (ht : 0 < t) :
      G t * (1 + (Real.sqrt t)⁻¹) =
        ∫ r in (0 : ℝ)..1, (1 + Real.sqrt t) / Δ (Real.sqrt t) r := by
    have hu : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    calc
      _ = (1 + (Real.sqrt t)⁻¹) *
          (∫ r in (0 : ℝ)..1, Real.sqrt t / Δ (Real.sqrt t) r) := by
            rw [hGrep t ht]
            ring
      _ = ∫ r in (0 : ℝ)..1,
          (1 + (Real.sqrt t)⁻¹) * (Real.sqrt t / Δ (Real.sqrt t) r) := by
            rw [← intervalIntegral.integral_const_mul]
      _ = ∫ r in (0 : ℝ)..1,
          (1 + Real.sqrt t) / Δ (Real.sqrt t) r := by
            apply intervalIntegral.integral_congr
            intro r hr
            have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
              simpa only [Set.uIcc_of_le zero_le_one] using hr
            field_simp [ne_of_gt hu, ne_of_gt (hDpos _ hu r hr')]
            <;> ring
  have hcont1 (u : ℝ) (hu : 0 < u) :
      ContinuousOn (fun r => u / Δ u r) (Set.uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hr
    exact ne_of_gt (hDpos u hu r hr')
  have hcont2 (u : ℝ) (hu : 0 < u) :
      ContinuousOn (fun r => (1 + u) / Δ u r) (Set.uIcc (0 : ℝ) 1) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hr
    exact ne_of_gt (hDpos u hu r hr')
  constructor
  · intro t ht
    dsimp [G, ψ]
    exact mul_pos (Real.sqrt_pos.2 ht)
      (RybinAI2026.P01.psi_integral_pos t ht)
  constructor
  · intro s hs t ht hst
    have hs' : 0 < s := Set.mem_Ioi.mp hs
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    have hu : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have hv : 0 < Real.sqrt t := Real.sqrt_pos.2 ht'
    have huv : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
    calc
      G s = ∫ r in (0 : ℝ)..1, Real.sqrt s / Δ (Real.sqrt s) r := hGrep s hs'
      _ ≤ ∫ r in (0 : ℝ)..1, Real.sqrt t / Δ (Real.sqrt t) r :=
        intervalIntegral.integral_mono_on zero_le_one
          (hcont1 _ hu).intervalIntegrable (hcont1 _ hv).intervalIntegrable
          (by
            intro r hr
            exact (RybinAI2026.P01.fractional_kernel_pointwise_order
              (Real.sqrt s) (Real.sqrt t) r hu huv hr).1)
      _ = G t := (hGrep t ht').symm
  · intro s hs t ht hst
    have hs' : 0 < s := Set.mem_Ioi.mp hs
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    have hu : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have hv : 0 < Real.sqrt t := Real.sqrt_pos.2 ht'
    have huv : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
    calc
      G t * (1 + (Real.sqrt t)⁻¹) =
          ∫ r in (0 : ℝ)..1, (1 + Real.sqrt t) / Δ (Real.sqrt t) r := hHrep t ht'
      _ ≤ ∫ r in (0 : ℝ)..1, (1 + Real.sqrt s) / Δ (Real.sqrt s) r :=
        intervalIntegral.integral_mono_on zero_le_one
          (hcont2 _ hv).intervalIntegrable (hcont2 _ hu).intervalIntegrable
          (by
            intro r hr
            exact (RybinAI2026.P01.fractional_kernel_pointwise_order
              (Real.sqrt s) (Real.sqrt t) r hu huv hr).2)
      _ = G s * (1 + (Real.sqrt s)⁻¹) := (hHrep s hs').symm
