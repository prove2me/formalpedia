-- Prove2me | Theorems.Thm_differentiableAt_eval_smul_resolvent
-- name    : differentiableAt_eval_smul_resolvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:49.225448+00:00
-- url     : https://prove2.me/theorems/0575ea72-88fb-5dd6-ab6e-1d6cbe4889a6
-- title:
--   differentiable At eval smul resolvent: differentiable At eval smul resolvent
-- statement:
--   `z ↦ p(z) • R_A(z)` is differentiable at every point of the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L60-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L60-L63

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem differentiableAt_eval_smul_resolvent (A : E →L[ℂ] E) (p : ℂ[X]) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) :
    DifferentiableAt ℂ (fun w : ℂ => p.eval w • resolvent A w) z := by sorry
