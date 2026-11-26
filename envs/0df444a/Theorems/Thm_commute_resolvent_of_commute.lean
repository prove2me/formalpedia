-- Prove2me | Theorems.Thm_commute_resolvent_of_commute
-- name    : commute_resolvent_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:31.11299+00:00
-- url     : https://prove2.me/theorems/73460367-c86b-5c81-80d7-97fb52af416b
-- title:
--   commute resolvent of commute: commute resolvent of commute
-- statement:
--   The commute resolvent of commute construction uses the commute resolvent of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L228-L235
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L228-L235

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

theorem commute_resolvent_of_commute
    (B D : E →L[ℂ] E) (z : ℂ) (hDB : Commute D B)
    (hres : z ∈ resolventSet ℂ B) :
    Commute D (resolvent B z) := by sorry
