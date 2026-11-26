-- Prove2me | solution 1 for ReweightedNPMLE.tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:12:39.866059+00:00
-- url     : https://prove2.me/submissions/659fa7c5-9d2e-4a80-87fd-b55eda4a5e77

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Scheffé's lemma for real probability densities.  Pointwise almost-everywhere
convergence, nonnegativity, and preservation of total mass upgrade to `L¹`
convergence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : ℕ → Ω → ℝ) (q : Ω → ℝ)
    (hpmeas : ∀ n, AEStronglyMeasurable (p n) μ)
    (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ n, ∀ᵐ x ∂μ, 0 ≤ p n x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : ∀ n, Integrable (p n) μ) (hqint : Integrable q μ)
    (hpone : ∀ n, ∫ x, p n x ∂μ = 1) (hqone : ∫ x, q x ∂μ = 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ p n x) atTop (𝓝 (q x))) :
    Tendsto (fun n ↦ ∫ x, |p n x - q x| ∂μ) atTop (𝓝 0) := by
  let m : ℕ → Ω → ℝ := fun n x ↦ min (p n x) (q x)
  have hmmeas : ∀ n, AEStronglyMeasurable (m n) μ := fun n ↦ by
    exact ((hpmeas n).aemeasurable.min hqmeas.aemeasurable).aestronglyMeasurable
  have hm_bound : ∀ n, ∀ᵐ x ∂μ, ‖m n x‖ ≤ q x := fun n ↦ by
    filter_upwards [hp n, hq] with x hpx hqx
    dsimp [m]
    rw [abs_of_nonneg (le_min hpx hqx)]
    exact min_le_right _ _
  have hm_lim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ m n x) atTop (𝓝 (q x)) := by
    filter_upwards [hlim] with x hx
    simpa only [m, min_self] using hx.min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ q x) atTop (𝓝 (q x)))
  have hm_integral :
      Tendsto (fun n ↦ ∫ x, m n x ∂μ) atTop (𝓝 1) := by
    have h := tendsto_integral_of_dominated_convergence q hmmeas hqint hm_bound hm_lim
    simpa only [hqone] using h
  have hmint : ∀ n, Integrable (m n) μ := fun n ↦
    hqint.mono' (hmmeas n) (hm_bound n)
  have hl1eq : ∀ n,
      (∫ x, |p n x - q x| ∂μ) = 2 - 2 * ∫ x, m n x ∂μ := by
    intro n
    calc
      (∫ x, |p n x - q x| ∂μ) =
          ∫ x, p n x + q x - 2 * m n x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rcases le_total (p n x) (q x) with hle | hle
        · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
          simp only [m, min_eq_left hle]
          ring
        · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
          simp only [m, min_eq_right hle]
          ring
      _ = (∫ x, p n x + q x ∂μ) - ∫ x, 2 * m n x ∂μ := by
        exact integral_sub ((hpint n).add hqint) ((hmint n).const_mul 2)
      _ = (∫ x, p n x ∂μ) + (∫ x, q x ∂μ) -
          2 * ∫ x, m n x ∂μ := by
        rw [integral_add (hpint n) hqint, integral_const_mul]
      _ = 2 - 2 * ∫ x, m n x ∂μ := by rw [hpone n, hqone]; ring
  rw [show (fun n ↦ ∫ x, |p n x - q x| ∂μ) =
      fun n ↦ 2 - 2 * ∫ x, m n x ∂μ by funext n; exact hl1eq n]
  simpa using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).sub
      (hm_integral.const_mul 2)
