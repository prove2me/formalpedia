-- Prove2me | Theorems.Thm_norm_eval_le_polynomialSupNorm
-- name    : norm_eval_le_polynomialSupNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:57.515968+00:00
-- url     : https://prove2.me/theorems/3583682f-62f4-4008-990e-892a8a5b9416
-- title:
--   norm eval le polynomial Sup Norm: norm eval le polynomial Sup Norm
-- statement:
--   If the values `‖p.eval z‖`, `z ∈ X`, are bounded above, then each of them is at most
--   `polynomialSupNorm p X`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L52-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L52-L63

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

theorem norm_eval_le_polynomialSupNorm (p : ℂ[X]) {X : Set ℂ}
    (hX : BddAbove ((fun z => ‖p.eval z‖) '' X)) {z : ℂ} (hz : z ∈ X) :
    ‖p.eval z‖ ≤ polynomialSupNorm p X := by sorry
