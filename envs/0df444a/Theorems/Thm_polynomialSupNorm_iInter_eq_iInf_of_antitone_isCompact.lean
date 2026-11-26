-- Prove2me | Theorems.Thm_polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact
-- name    : polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:24.537461+00:00
-- url     : https://prove2.me/theorems/4a5a00a9-0bc5-4454-a318-2ac7bb096932
-- title:
--   polynomial Sup Norm i Inter eq i Inf of antitone is Compact: polynomial Sup Norm i Inter eq i Inf of antitone is Compact
-- statement:
--   The polynomial sup-norm on the intersection of a decreasing sequence of
--   nonempty compact sets is the infimum of the sup-norms on those sets.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L58-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L58-L112

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
set_option autoImplicit false
open Filter Polynomial Set

theorem polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact
    (p : Polynomial ℂ) (K : ℕ → Set ℂ)
    (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty) :
    polynomialSupNorm p (⋂ n, K n) =
      ⨅ n, polynomialSupNorm p (K n) := by sorry
