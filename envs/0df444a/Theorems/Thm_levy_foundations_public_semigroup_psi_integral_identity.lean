-- Prove2me | Theorems.Thm_levy_foundations_public_semigroup_psi_integral_identity
-- name    : levy_foundations_public_semigroup_psi_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:04:08.089459+00:00
-- url     : https://prove2.me/theorems/f90c94ba-969f-4ce6-9ddb-cfaa76de073c
-- title:
--   Identify the semigroup exponent from the common small-time limits
-- statement:
--   Source-faithful public statement of LeanLevy ConvolutionSemigroup.psi_eq_levyKhintchine_formula. Assuming common small-time limits for drift, variance and annulus test functions at a radius without Lévy-measure atoms, identify the exponent exactly including the drift correction, Gaussian small-ball second-moment correction and compensated jump integral. The proof combines the scaled characteristic-function limit, drift/small-jump/large-jump limits and ν-side algebra.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

theorem levy_foundations_public_semigroup_psi_integral_identity
    (S : ProbabilityTheory.ConvolutionSemigroup)
    {r : ℝ} (hr : r ∈ Set.Ioc (1 / 2 : ℝ) 1)
    (b_r : ℝ) (σ_sq_r : ℝ≥0)
    {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht_seq : Filter.Tendsto (fun n => (t_seq n).val)
      Filter.atTop (nhds (0 : ℝ)))
    (hb : Filter.Tendsto (fun n => (t_seq n).val⁻¹ *
      ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
      Filter.atTop (nhds b_r))
    (hσ : Filter.Tendsto (fun n => (t_seq n).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
      Filter.atTop (nhds (σ_sq_r : ℝ)))
    (h_jump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
      Filter.Tendsto (fun n => (t_seq n).val⁻¹ *
        ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
        Filter.atTop (nhds (∫ x, f x ∂ν)))
    (ξ : ℝ) :
    S.exponent ξ =
      ↑(b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * Complex.I
      - ↑((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) * ↑ξ ^ 2 / 2
      + ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν := by
  sorry
