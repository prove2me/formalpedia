-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval
-- name    : norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:45:36.224057+00:00
-- url     : https://prove2.me/theorems/25c64048-e05c-43e3-b887-f51e8777c715
-- title:
--   norm aeval le polynomial Sup Norm of is Star Normal aeval: norm aeval le polynomial Sup Norm of is Star Normal aeval
-- statement:
--   If the single element `p(a)` is normal and `K` is compact with `K ⊇ σ(a)`, then
--   `‖p(a)‖ ≤ polynomialSupNorm p K`.  Normality of `a` itself is not needed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/Normal.lean#L24-L40
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/Normal.lean#L24-L40

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_Normal
set_option autoImplicit false
open Polynomial

theorem norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval {A : Type*} [CStarAlgebra A]
    (a : A) {K : Set ℂ} (hK : IsCompact K) (hσ : spectrum ℂ a ⊆ K)
    (p : ℂ[X]) [IsStarNormal (aeval a p)] :
    ‖aeval a p‖ ≤ polynomialSupNorm p K := by sorry
