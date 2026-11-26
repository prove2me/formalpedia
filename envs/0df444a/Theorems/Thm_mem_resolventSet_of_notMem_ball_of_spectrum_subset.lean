-- Prove2me | Theorems.Thm_mem_resolventSet_of_notMem_ball_of_spectrum_subset
-- name    : mem_resolventSet_of_notMem_ball_of_spectrum_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:30.598841+00:00
-- url     : https://prove2.me/theorems/ecc587e7-717f-5b5c-a618-49821b8b9269
-- title:
--   mem resolvent Set of not Mem ball of spectrum subset: mem resolvent Set of not Mem ball of spectrum subset
-- statement:
--   Points outside an open disk containing the spectrum lie in the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L53-L57
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L53-L57

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]

theorem mem_resolventSet_of_notMem_ball_of_spectrum_subset (A : E →L[ℂ] E) {c : ℂ} {r : ℝ}
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) {z : ℂ} (hz : z ∉ Metric.ball c r) :
    z ∈ resolventSet ℂ A := by sorry
