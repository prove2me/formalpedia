-- Prove2me | solution 3 for MarkovChainCLT.clt_of_uniformly_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:40:06.149767+00:00
-- url     : https://prove2.me/submissions/a4fd2e89-50bd-4444-a231-0a69a486e8a4

import Theorems.Thm_MarkovChainCLT_martingaleCLT_chain
import Theorems.Thm_MarkovChainCLT_poissonEquation_ae_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_stationary_clt_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_tendstoInMeasure_inv_sqrt_coord_sub

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (huni : UniformlyErgodic P π) (hL2 : MemLp f 2 π) :
    SatisfiesCLT P π f := by
  obtain ⟨g, hgm, hgL2, hGm, hPgL2, hpois⟩ := poissonEquation_ae_of_uniformlyErgodic P π hP huni f hf hL2
  obtain ⟨v, hmart⟩ := martingaleCLT_chain P π hP g hgm hgL2
  set G : X → ℝ := fun x => ∫ y, g y ∂(P x) with hG
  -- lift the π-a.e. Poisson identity to: a.s. it holds at *every* coordinate at once
  have hae : ∀ᵐ ω ∂(chainMeasure P π), ∀ i : ℕ,
      g (ω i) - G (ω i) = f (ω i) - ∫ x, f x ∂π := by
    rw [ae_all_iff]
    intro i
    refine ae_of_ae_map (f := fun ω : ℕ → X => ω i)
      (p := fun y => g y - G y = f y - ∫ x, f x ∂π) (measurable_pi_apply i).aemeasurable ?_
    rw [map_coord_chainMeasure P π hP.1 i]
    exact hpois
  -- the martingale approximation, pointwise on each path
  have hdecomp : ∀ᵐ ω ∂(chainMeasure P π), ∀ (n : ℕ),
      Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (g (ω (i + 1)) - G (ω i))
        = (Real.sqrt n)⁻¹ * (G (ω 0) - G (ω n)) := by
    filter_upwards [hae] with ω hω n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleAvg]
    · have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
      have hnn : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have key : ∑ i ∈ Finset.range n, ((f (ω (i + 1)) - ∫ x, f x ∂π) - (g (ω (i+1)) - G (ω i)))
          = G (ω 0) - G (ω n) := by
        have : ∀ i, ((f (ω (i + 1)) - ∫ x, f x ∂π) - (g (ω (i+1)) - G (ω i)))
            = G (ω i) - G (ω (i + 1)) := by
          intro i
          have := hω (i + 1)
          simp only [hG] at this ⊢
          linarith
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_range_sub' (fun i => G (ω i)) n]
      have hsamp : Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)
          = (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (f (ω (i + 1)) - ∫ x, f x ∂π) := by
        rw [sampleAvg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        field_simp
        rw [Real.sq_sqrt (by positivity)]
        ring
      rw [hsamp, ← mul_sub, ← Finset.sum_sub_distrib, key]
  -- the remainder vanishes in probability
  have hGL1 : Integrable G π := hPgL2.integrable (by norm_num)
  have hD := tendstoInMeasure_inv_sqrt_coord_sub P π hP G hGm hGL1
  have hsub : ∀ n : ℕ, (fun ω : ℕ → X => (Real.sqrt n)⁻¹ * (G (ω 0) - G (ω n)))
      =ᵐ[chainMeasure P π]
      ((fun (m : ℕ) (ω : ℕ → X) => Real.sqrt m * (sampleAvg f m ω - ∫ x, f x ∂π))
        - (fun (m : ℕ) (ω : ℕ → X) =>
            (Real.sqrt m)⁻¹ * ∑ i ∈ Finset.range m, (g (ω (i + 1)) - G (ω i)))) n := by
    intro n
    filter_upwards [hdecomp] with ω hω
    exact (hω n).symm
  -- Slutsky
  refine satisfiesCLT_of_stationary_clt_of_uniformlyErgodic P π huni f hf v ?_
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hmart
    (TendstoInMeasure.congr hsub (by rfl) hD) (fun n => ?_)
  exact (((Finset.measurable_fun_sum _
    (fun i _ => hf.comp (measurable_pi_apply (i + 1)))).const_mul _).sub_const _).const_mul _
    |>.aemeasurable
