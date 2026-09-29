-- Prove2me | solution 1 for BanditAlgorithm.le_of_ae_discounted_permutation_approximations
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T03:47:54.244821+00:00
-- url     : https://prove2.me/submissions/490ce329-a186-46e1-9c9c-434e9ceb2dbf

import Theorems.Thm_BanditAlgorithm_discounted_list_value_le_of_perm_pairwise
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open BanditAlgorithm

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α u v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcert : ∀ ε : ℝ, 0 < ε →
      ∃ xs ys : Ω → List ℝ,
        (∀ᵐ ω ∂μ, (xs ω).Perm (ys ω) ∧
          (ys ω).Pairwise (· ≥ ·)) ∧
        Integrable (fun ω ↦ (xs ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
        Integrable (fun ω ↦ (ys ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
        u ≤ (∫ ω, (xs ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) + ε ∧
        (∫ ω, (ys ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) ≤ v + ε) :
    u ≤ v := by
  by_contra huv
  have hvu : v < u := lt_of_not_ge huv
  let ε : ℝ := (u - v) / 4
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨xs, ys, hpoint, hxint, hyint, huxs, hysv⟩ := hcert ε hε
  have hint :
      (∫ ω, (xs ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) ≤
        ∫ ω, (ys ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ := by
    apply integral_mono_ae hxint hyint
    filter_upwards [hpoint] with ω hω
    exact discounted_list_value_le_of_perm_pairwise
      hα0 hα1 hω.1 hω.2
  dsimp [ε] at huxs hysv
  linarith
