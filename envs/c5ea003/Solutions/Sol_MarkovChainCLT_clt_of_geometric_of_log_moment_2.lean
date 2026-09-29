-- Prove2me | solution 2 for MarkovChainCLT.clt_of_geometric_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T01:28:00.886413+00:00
-- url     : https://prove2.me/submissions/9db0e7a4-fb1c-40e2-b464-0fcefc88aa2a

import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_centered_functional_clt
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_exp_of_geometricallyErgodic
import Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const
import Theorems.Thm_MarkovChainCLT_clt_of_exp_alpha_of_log_moment

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hgeo : GeometricallyErgodic P π)
    (hmom : Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) :
    SatisfiesCLT P π f := by
  have hgm : Measurable (fun x => f x - ∫ x, f x ∂π) := hf.sub_const _
  -- (0) the moment condition gives L² and survives centring
  obtain ⟨hL2, hmomC⟩ :=
    memLp_two_and_logMoment_sub_const π f hf hmom (∫ x, f x ∂π)
  -- (1) geometric ergodicity gives exponentially fast strong mixing of the stationary chain
  obtain ⟨c, a, hc0, ha0, ha1, hα⟩ := alphaMixingCoef_exp_of_geometricallyErgodic P π hP hgeo
  -- (2) the functional process inherits the bound
  have hdom : ∀ n : ℕ,
      0 ≤ alphaMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n ∧
      alphaMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n
        ≤ alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n := fun n =>
    alphaMixingCoef_comp_nonneg_le_of_finite (chainMeasure P π) (fun i (ω : ℕ → X) => ω i)
      (fun x => f x - ∫ x, f x ∂π) hgm n
  have hexp : ∀ n : ℕ,
      alphaMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n ≤ c * a ^ n :=
    fun n => (hdom n).2.trans (hα n)
  -- (3) stationarity, centring, and the log-moment on the path space
  have hstat0 : IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) :=
    isStrictlyStationary_coord_chainMeasure P π hP.1
  have hstat : IsStrictlyStationary (chainMeasure P π)
      (fun i ω => f (ω i) - ∫ x, f x ∂π) :=
    isStrictlyStationary_comp_of_measurable _ _ (fun n => measurable_pi_apply n) hstat0 _ hgm
  have hmap := map_coord_chainMeasure P π hP.1 0
  have hmeas : AEMeasurable (fun ω : ℕ → X => ω 0) (chainMeasure P π) :=
    (measurable_pi_apply 0).aemeasurable
  have hfint : Integrable f π := hL2.integrable (by norm_num)
  have h1 : ∫ ω, f (ω 0) ∂(chainMeasure P π) = ∫ x, f x ∂π := by
    conv_rhs => rw [← hmap]
    rw [integral_map hmeas hf.aestronglyMeasurable]
  have h2 : Integrable (fun ω : ℕ → X => f (ω 0)) (chainMeasure P π) := by
    have hi : Integrable f (Measure.map (fun ω : ℕ → X => ω 0) (chainMeasure P π)) := by
      rw [hmap]; exact hfint
    exact (integrable_map_measure hf.aestronglyMeasurable hmeas).mp hi
  have hcent : ∫ ω, (f (ω 0) - ∫ x, f x ∂π) ∂(chainMeasure P π) = 0 := by
    rw [integral_sub h2 (integrable_const _), h1, integral_const]
    simp
  have hYmeas : ∀ n : ℕ, Measurable (fun ω : ℕ → X => f (ω n) - ∫ x, f x ∂π) := fun n =>
    (hf.comp (measurable_pi_apply n)).sub_const _
  have hmomPath : Integrable (fun ω : ℕ → X =>
      (f (ω 0) - ∫ x, f x ∂π) ^ 2 * Real.posLog |f (ω 0) - ∫ x, f x ∂π|)
      (chainMeasure P π) := by
    have hi : Integrable (fun x => (f x - ∫ x, f x ∂π) ^ 2 * Real.posLog |f x - ∫ x, f x ∂π|)
        (Measure.map (fun ω : ℕ → X => ω 0) (chainMeasure P π)) := by
      rw [hmap]; exact hmomC
    exact (integrable_map_measure hi.aestronglyMeasurable hmeas).mp hi
  -- (4) Theorem 6 (Doukhan–Massart–Rio), then Remark 6
  have hthm6 := clt_of_exp_alpha_of_log_moment (chainMeasure P π)
    (fun i ω => f (ω i) - ∫ x, f x ∂π) hYmeas hstat hcent c a ha0 ha1 hexp hmomPath
  exact satisfiesCLT_of_centered_functional_clt P π hP f hf hL2 hthm6.1 hthm6.2
