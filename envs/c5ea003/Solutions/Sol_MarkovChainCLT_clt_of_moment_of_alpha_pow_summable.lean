-- Prove2me | solution 1 for MarkovChainCLT.clt_of_moment_of_alpha_pow_summable
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T23:09:25.87738+00:00
-- url     : https://prove2.me/submissions/fbdd509e-33c0-4c29-a3be-f3ebd733b7db

import Theorems.Thm_MarkovChainCLT_summable_covariance_of_alpha_pow_summable
import Theorems.Thm_MarkovChainCLT_tendstoInDistribution_of_alpha_pow_summable

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Jones (2004), Theorem 5, condition 2 (Ibragimov–Linnik moment case), reduced to the
covariance-summability and distributional-limit components. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by
  have hsum := MarkovChainCLT.summable_covariance_of_alpha_pow_summable
    P Y hY hstat hcent δ hδ hmom hα
  refine ⟨hsum, fun hvar => ?_⟩
  exact MarkovChainCLT.tendstoInDistribution_of_alpha_pow_summable
    P Y hY hstat hcent δ hδ hmom hα hsum hvar
