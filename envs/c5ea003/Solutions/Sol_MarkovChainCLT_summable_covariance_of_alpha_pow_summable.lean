-- Prove2me | solution 1 for MarkovChainCLT.summable_covariance_of_alpha_pow_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:30:38.963536+00:00
-- url     : https://prove2.me/submissions/859f7dc5-22ae-423c-930b-52c4fe6876a7

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_alpha_cov_bound_of_moment
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  obtain ⟨C, _, hbound⟩ :=
    MarkovChainCLT.alpha_cov_bound_of_moment P Y hY hstat hcent δ hδ hmom
  have hsum : Summable (fun k : ℕ => C * alphaMixingCoef P Y (k + 1) ^ (δ / (2 + δ))) :=
    ((summable_nat_add_iff 1).2 hα).mul_left C
  exact Summable.of_norm_bounded hsum fun k => by simpa using hbound k
