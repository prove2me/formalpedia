-- Prove2me | Theorems.Thm_adjoint_aeval_apply_of_forall_pow
-- name    : adjoint_aeval_apply_of_forall_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:55.029586+00:00
-- url     : https://prove2.me/theorems/36022dda-e4e0-5d46-8f4f-c294a9f57dd4
-- title:
--   adjoint aeval apply of forall pow: adjoint aeval apply of forall pow
-- statement:
--   If `V† U^n V = T^n` for all `n`, then `V† p(U) V = p(T)` for every polynomial `p`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L107-L111
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L107-L111

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem adjoint_aeval_apply_of_forall_pow (T : E →L[ℂ] E) (V : E →L[ℂ] H) (U : H →L[ℂ] H)
    (hpow : ∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x) (p : ℂ[X]) (x : E) :
    adjoint V ((aeval U p) (V x)) = (aeval T p) x := by sorry
