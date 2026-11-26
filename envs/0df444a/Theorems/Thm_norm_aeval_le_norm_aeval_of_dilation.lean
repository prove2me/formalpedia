-- Prove2me | Theorems.Thm_norm_aeval_le_norm_aeval_of_dilation
-- name    : norm_aeval_le_norm_aeval_of_dilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:03.819419+00:00
-- url     : https://prove2.me/theorems/0c857bda-d6cd-5731-a416-4f94db9d4a84
-- title:
--   norm aeval le norm aeval of dilation: norm aeval le norm aeval of dilation
-- statement:
--   If `V` preserves inner products and `V† U^n V = T^n` for all `n`, then
--   `‖p(T)‖ ≤ ‖p(U)‖` for every polynomial `p`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L115-L128
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L115-L128

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

theorem norm_aeval_le_norm_aeval_of_dilation (T : E →L[ℂ] E) (V : E →L[ℂ] H) (U : H →L[ℂ] H)
    (hV : ∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hpow : ∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ ‖aeval U p‖ := by sorry
