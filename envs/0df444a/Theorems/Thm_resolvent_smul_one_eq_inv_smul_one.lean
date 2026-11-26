-- Prove2me | Theorems.Thm_resolvent_smul_one_eq_inv_smul_one
-- name    : resolvent_smul_one_eq_inv_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:37.529251+00:00
-- url     : https://prove2.me/theorems/9efa92fe-6aa7-5031-a435-225626d3d246
-- title:
--   resolvent smul one eq inv smul one: resolvent smul one eq inv smul one
-- statement:
--   The resolvent smul one eq inv smul one construction uses the resolvent smul one eq inv smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L413-L426
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L413-L426

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]

theorem resolvent_smul_one_eq_inv_smul_one
    [Nontrivial E] (c z : ℂ) (hz : z ≠ c) :
    resolvent (c • (1 : E →L[ℂ] E)) z =
      (z - c)⁻¹ • (1 : E →L[ℂ] E) := by sorry
