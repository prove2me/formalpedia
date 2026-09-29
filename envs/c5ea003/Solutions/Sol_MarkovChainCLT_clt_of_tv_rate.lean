-- Prove2me | solution 1 for MarkovChainCLT.clt_of_tv_rate
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:52:07.023259+00:00
-- url     : https://prove2.me/submissions/5f2a6032-b894-4029-93e7-9afb2e2d90a6

import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_centered_functional_clt
import Theorems.Thm_MarkovChainCLT_alpha_mixing_le_tv_rate
import Theorems.Thm_MarkovChainCLT_clt_of_moment_of_alpha_pow_summable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (M : X → ℝ) (hM0 : ∀ x, 0 ≤ M x) (hM : Integrable M π)
    (γ : ℕ → ℝ) (hγ0 : ∀ n, 0 ≤ γ n) (hγa : Antitone γ)
    (hrate : ErgodicWithRate P π M γ)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun x => |f x| ^ (2 + δ)) π)
    (hsum : Summable (fun n => γ n ^ (δ / (2 + δ)))) :
    SatisfiesCLT P π f := by
  have hgm : Measurable (fun x => f x - ∫ x, f x ∂π) := hf.sub_const _
  have h2δ : (0:ℝ) < 2 + δ := by linarith
  set p : ℝ≥0∞ := ENNReal.ofReal (2 + δ) with hp
  have hp0 : p ≠ 0 := by simp [hp]; linarith
  have hpt : p ≠ ∞ := by simp [hp]
  have hptoreal : p.toReal = 2 + δ := by rw [hp, ENNReal.toReal_ofReal h2δ.le]
  -- (0) moment hypotheses in MemLp form
  have hfp : MemLp f p π := by
    refine (integrable_norm_rpow_iff hf.aestronglyMeasurable hp0 hpt).mp ?_
    have hfun : (fun x => ‖f x‖ ^ p.toReal) = (fun x => |f x| ^ (2 + δ)) := by
      funext x; rw [hptoreal, Real.norm_eq_abs]
    rw [hfun]; exact hmom
  have hL2 : MemLp f 2 π := by
    refine hfp.mono_exponent ?_
    rw [hp, show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- (1) Theorem 2(ii): a total-variation rate bounds the strong mixing coefficients
  have hmix := alpha_mixing_le_tv_rate P π hP M hM0 hM γ hγ0 hrate
  -- (2) the functional process inherits the bound
  have hdom : ∀ n : ℕ,
      0 ≤ alphaMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n ∧
      alphaMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n
        ≤ alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n := fun n =>
    alphaMixingCoef_comp_nonneg_le_of_finite (chainMeasure P π) (fun i (ω : ℕ → X) => ω i)
      (fun x => f x - ∫ x, f x ∂π) hgm n
  -- (3) eq. (11) transfers to the functional process
  have hMint : (0:ℝ) ≤ ∫ x, M x ∂π := integral_nonneg hM0
  have he : (0:ℝ) ≤ δ / (2 + δ) := le_of_lt (div_pos hδ h2δ)
  have hα : Summable (fun n =>
      alphaMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n
        ^ (δ / (2 + δ))) := by
    rw [← summable_nat_add_iff 1]
    have hcomp : Summable (fun n : ℕ =>
        (∫ x, M x ∂π) ^ (δ / (2 + δ)) * γ (n + 1) ^ (δ / (2 + δ))) := by
      exact (((summable_nat_add_iff 1).mpr hsum)).mul_left _
    refine hcomp.of_nonneg_of_le
      (fun n => Real.rpow_nonneg (hdom (n + 1)).1 _) (fun n => ?_)
    have hle : alphaMixingCoef (chainMeasure P π)
        (fun i ω => f (ω i) - ∫ x, f x ∂π) (n + 1) ≤ γ (n + 1) * ∫ x, M x ∂π :=
      le_trans (hdom (n + 1)).2 (hmix (n + 1) (by omega))
    calc alphaMixingCoef (chainMeasure P π)
          (fun i ω => f (ω i) - ∫ x, f x ∂π) (n + 1) ^ (δ / (2 + δ))
        ≤ (γ (n + 1) * ∫ x, M x ∂π) ^ (δ / (2 + δ)) :=
          Real.rpow_le_rpow (hdom (n + 1)).1 hle he
      _ = (∫ x, M x ∂π) ^ (δ / (2 + δ)) * γ (n + 1) ^ (δ / (2 + δ)) := by
          rw [Real.mul_rpow (hγ0 _) hMint]; ring
  -- (4) stationarity, centring, moments on the path space
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
  have hYp : MemLp (fun ω : ℕ → X => f (ω 0) - ∫ x, f x ∂π) p (chainMeasure P π) := by
    have hm : MemLp f p (Measure.map (fun ω : ℕ → X => ω 0) (chainMeasure P π)) := by
      rw [hmap]; exact hfp
    exact ((memLp_map_measure_iff hf.aestronglyMeasurable hmeas).mp hm).sub (memLp_const _)
  have hYmom : Integrable
      (fun ω : ℕ → X => |f (ω 0) - ∫ x, f x ∂π| ^ (2 + δ)) (chainMeasure P π) := by
    simpa [Real.norm_eq_abs, hptoreal] using hYp.integrable_norm_rpow hp0 hpt
  -- (5) Theorem 5(ii) (Ibragimov–Linnik), then Remark 6
  have hthm5 := clt_of_moment_of_alpha_pow_summable (chainMeasure P π)
    (fun i ω => f (ω i) - ∫ x, f x ∂π) hYmeas hstat hcent δ hδ hYmom hα
  exact satisfiesCLT_of_centered_functional_clt P π hP f hf hL2 hthm5.1 hthm5.2
