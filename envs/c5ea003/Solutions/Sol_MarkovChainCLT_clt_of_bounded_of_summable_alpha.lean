-- Prove2me | solution 1 for MarkovChainCLT.clt_of_bounded_of_summable_alpha
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T23:22:15.109774+00:00
-- url     : https://prove2.me/submissions/b2a9070f-d273-4f06-955b-31531eb05c84

import Theorems.Thm_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha
import Theorems.Thm_MarkovChainCLT_tendstoInDistribution_of_bounded_of_summable_alpha

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Jones (2004), Theorem 5, condition 1 (Ibragimov–Linnik bounded case), reduced to the
covariance-summability and distributional-limit components. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by
  have hsum := MarkovChainCLT.summable_covariance_of_bounded_of_summable_alpha
    P Y hY hstat hcent B hB hα
  refine ⟨hsum, fun hvar => ?_⟩
  exact MarkovChainCLT.tendstoInDistribution_of_bounded_of_summable_alpha
    P Y hY hstat hcent B hB hα hsum hvar
