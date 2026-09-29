-- Prove2me | solution 1 for MarkovChainCLT.clt_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T23:43:34.41294+00:00
-- url     : https://prove2.me/submissions/1730fdd9-19b4-442c-95c2-43e9109eacb2

import Theorems.Thm_MarkovChainCLT_summable_covariance_of_exp_alpha_of_log_moment
import Theorems.Thm_MarkovChainCLT_tendstoInDistribution_of_exp_alpha_of_log_moment

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Jones (2004), Theorem 6 (Doukhan–Massart–Rio), reduced to the covariance-summability
and distributional-limit components. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by
  have hsum := MarkovChainCLT.summable_covariance_of_exp_alpha_of_log_moment
    P Y hY hstat hcent c a ha0 ha1 hα hmom
  refine ⟨hsum, fun hvar => ?_⟩
  exact MarkovChainCLT.tendstoInDistribution_of_exp_alpha_of_log_moment
    P Y hY hstat hcent c a ha0 ha1 hα hmom hsum hvar
