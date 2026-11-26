-- Prove2me | Theorems.Thm_tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
-- name    : tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:28.667236+00:00
-- url     : https://prove2.me/theorems/6b26c04c-04bf-5c63-b7fb-81a45a0250e6
-- title:
--   tendsto polynomial Sup Norm at Top of antitone is Compact: tendsto polynomial Sup Norm at Top of antitone is Compact
-- statement:
--   Along a decreasing sequence of nonempty compact sets, polynomial
--   sup-norms converge to the sup-norm on the intersection.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L116-L130
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L116-L130

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
set_option autoImplicit false
open Filter Polynomial Set

theorem tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
    (p : Polynomial ℂ) (K : ℕ → Set ℂ)
    (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty) :
    Tendsto (fun n ↦ polynomialSupNorm p (K n)) atTop
      (nhds (polynomialSupNorm p (⋂ n, K n))) := by sorry
