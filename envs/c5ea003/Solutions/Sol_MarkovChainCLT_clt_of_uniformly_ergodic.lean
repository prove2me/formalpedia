-- Prove2me | solution 1 for MarkovChainCLT.clt_of_uniformly_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:52:06.549214+00:00
-- url     : https://prove2.me/submissions/dcf8c28a-c4a9-441c-bc90-78cf29dc18e9

import Theorems.Thm_MarkovChainCLT_phiMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_centered_functional_clt
import Theorems.Thm_MarkovChainCLT_uniformlyErgodic_phiMixing_exp
import Theorems.Thm_MarkovChainCLT_clt_of_summable_sqrt_phi

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (huni : UniformlyErgodic P π) (hL2 : MemLp f 2 π) :
    SatisfiesCLT P π f := by
  have hgm : Measurable (fun x => f x - ∫ x, f x ∂π) := hf.sub_const _
  -- (a) uniform ergodicity gives exponentially fast φ-mixing
  obtain ⟨c, θ, hc, hθ, hbd⟩ := uniformlyErgodic_phiMixing_exp P π hP huni
  -- (b) the centred functional process inherits the rate
  have hdom : ∀ n : ℕ,
      0 ≤ phiMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n ∧
      phiMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n
        ≤ phiMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n := fun n =>
    phiMixingCoef_comp_nonneg_le_of_finite (chainMeasure P π) (fun i (ω : ℕ → X) => ω i)
      (fun x => f x - ∫ x, f x ∂π) hgm n
  -- (c) eq. (13): summability of √φ
  have hgs : ∀ K r : ℝ, 0 < r → Summable (fun n : ℕ => K * Real.exp (-r * ((n + 1 : ℕ) : ℝ))) := by
    intro K r hr
    have hlt : |Real.exp (-r)| < 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have hs := (summable_geometric_of_abs_lt_one hlt).mul_left (K * Real.exp (-r))
    refine hs.congr fun n => ?_
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    push_cast
    congr 1
    ring
  have hsqrtexp : ∀ y : ℝ, Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
    intro y
    have h : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← h, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hφ : Summable (fun n =>
      Real.sqrt (phiMixingCoef (chainMeasure P π)
        (fun i ω => f (ω i) - ∫ x, f x ∂π) n)) := by
    rw [← summable_nat_add_iff 1]
    refine (hgs (Real.sqrt c) (θ / 2) (by linarith)).of_nonneg_of_le
      (fun n => Real.sqrt_nonneg _) (fun n => ?_)
    have h1 : phiMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) (n + 1)
        ≤ c * Real.exp (-θ * ((n + 1 : ℕ) : ℝ)) :=
      le_trans (hdom (n + 1)).2 (hbd (n + 1) (by omega))
    calc Real.sqrt (phiMixingCoef (chainMeasure P π)
            (fun i ω => f (ω i) - ∫ x, f x ∂π) (n + 1))
        ≤ Real.sqrt (c * Real.exp (-θ * ((n + 1 : ℕ) : ℝ))) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt c * Real.exp (-(θ / 2) * ((n + 1 : ℕ) : ℝ)) := by
          rw [Real.sqrt_mul hc, hsqrtexp]; congr 1; ring
  -- (d) stationarity, centring, square-integrability
  have hstat0 : IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) :=
    isStrictlyStationary_coord_chainMeasure P π hP.1
  have hstat : IsStrictlyStationary (chainMeasure P π)
      (fun i ω => f (ω i) - ∫ x, f x ∂π) :=
    isStrictlyStationary_comp_of_measurable _ _ (fun n => measurable_pi_apply n) hstat0 _ hgm
  have hmap := map_coord_chainMeasure P π hP.1 0
  have hfint : Integrable f π := hL2.integrable (by norm_num)
  have hmeas : AEMeasurable (fun ω : ℕ → X => ω 0) (chainMeasure P π) :=
    (measurable_pi_apply 0).aemeasurable
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
  have hYL2 : MemLp (fun ω : ℕ → X => f (ω 0) - ∫ x, f x ∂π) 2 (chainMeasure P π) := by
    have hm : MemLp f 2 (Measure.map (fun ω : ℕ → X => ω 0) (chainMeasure P π)) := by
      rw [hmap]; exact hL2
    exact ((memLp_map_measure_iff hf.aestronglyMeasurable hmeas).mp hm).sub (memLp_const _)
  -- (e) Theorem 8 (Billingsley's φ-mixing CLT), then Remark 6
  have hthm8 := clt_of_summable_sqrt_phi (chainMeasure P π)
    (fun i ω => f (ω i) - ∫ x, f x ∂π) hYmeas hstat hcent hYL2 hφ
  exact satisfiesCLT_of_centered_functional_clt P π hP f hf hL2 hthm8.1 hthm8.2
