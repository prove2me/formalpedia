-- Prove2me | Theorems.Thm_resolvent_sub_smul_one_shift
-- name    : resolvent_sub_smul_one_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:34.730617+00:00
-- url     : https://prove2.me/theorems/04f8c394-8e76-462a-bbea-608ee456360b
-- title:
--   resolvent sub smul one shift: resolvent sub smul one shift
-- statement:
--   Translating both the operator and spectral parameter by `c` leaves the
--   resolvent unchanged.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L476-L481
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L476-L481

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]

theorem resolvent_sub_smul_one_shift (A : E →L[ℂ] E) (c z : ℂ) :
    resolvent (A - c • (1 : E →L[ℂ] E)) z = resolvent A (z + c) := by sorry
