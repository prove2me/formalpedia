-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_of_isStarNormal
-- name    : norm_aeval_le_polynomialSupNorm_of_isStarNormal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:45:19.851258+00:00
-- url     : https://prove2.me/theorems/c2509dd3-4ab1-54cb-ad47-319051003828
-- title:
--   norm aeval le polynomial Sup Norm of is Star Normal: norm aeval le polynomial Sup Norm of is Star Normal
-- statement:
--   For a normal element `a` of a C*-algebra and a compact `K ⊇ σ(a)`,
--   `‖p(a)‖ ≤ polynomialSupNorm p K`: `p(a)` is normal, so `‖p(a)‖` is its spectral radius, and
--   `σ(p(a)) = p(σ(a))` by the spectral mapping theorem.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/Normal.lean#L45-L52
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/Normal.lean#L45-L52

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_Normal
set_option autoImplicit false
open Polynomial

theorem norm_aeval_le_polynomialSupNorm_of_isStarNormal {A : Type*} [CStarAlgebra A]
    (a : A) [IsStarNormal a] {K : Set ℂ} (hK : IsCompact K) (hσ : spectrum ℂ a ⊆ K)
    (p : ℂ[X]) : ‖aeval a p‖ ≤ polynomialSupNorm p K := by sorry
