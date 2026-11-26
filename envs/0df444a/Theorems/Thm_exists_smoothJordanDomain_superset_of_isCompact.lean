-- Prove2me | Theorems.Thm_exists_smoothJordanDomain_superset_of_isCompact
-- name    : exists_smoothJordanDomain_superset_of_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:33:51.256409+00:00
-- url     : https://prove2.me/theorems/6cea30f6-5e87-490b-8914-ca2f63fa69c9
-- title:
--   exists smooth Jordan Domain superset of is Compact: exists smooth Jordan Domain superset of is Compact
-- statement:
--   Every compact subset of `ℂ` lies in a smooth strictly convex Jordan domain.
--
--   This is the one-domain existence result consumed by the initial auxiliary
--   operator construction.  It does not provide the nested exhaustion whose
--   intersection is `K`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean#L65-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean#L65-L68

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem exists_smoothJordanDomain_superset_of_isCompact (K : Set ℂ) (hK : IsCompact K) :
    ∃ Ω : SmoothJordanDomain, K ⊆ Ω.carrier := by sorry
