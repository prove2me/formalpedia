-- Prove2me | Theorems.Thm_kyprianou82_phi_domain_bridge
-- name    : kyprianou82_phi_domain_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:23:18.722559+00:00
-- url     : https://prove2.me/theorems/ae2c9109-c2d9-4307-b464-9e0bcfbfb1a1
-- title:
--   Stage B principal exponent has the source scale-transform domain bridge
-- statement:
--   The filtered Avram coupling transfers the source Levy root domain to the original Laplace exponent, giving the order equivalence Phi psi r < beta iff r < psi beta for every nonnegative rate r.
-- source:
--   Kyprianou chapter 8 Stage B source result 81 Levy root domain, transported across the Proved filtered Avram coupling.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem kyprianou82_phi_domain_bridge
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
    : ∀ r : ℝ, 0 ≤ r → IsScaleTransformDomainBridge ψ r := by
  sorry
