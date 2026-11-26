-- Prove2me | Theorems.Thm_exists_polynomial_tendstoUniformlyOn_inv_sub_of_isCompact_convex
-- name    : exists_polynomial_tendstoUniformlyOn_inv_sub_of_isCompact_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:43.777119+00:00
-- url     : https://prove2.me/theorems/a0550b40-1268-5378-be16-17da116fa141
-- title:
--   exists polynomial tendsto Uniformly On inv sub of is Compact convex: exists polynomial tendsto Uniformly On inv sub of is Compact convex
-- statement:
--   On a compact convex planar set, every Cauchy kernel with exterior pole is
--   a compact-uniform limit of complex polynomials.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRunge.lean#L159-L240
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRunge.lean#L159-L240

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_Operator_Crouzeix_ConvexRunge
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Topology

theorem exists_polynomial_tendstoUniformlyOn_inv_sub_of_isCompact_convex
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    {ζ : ℂ} (hζ : ζ ∉ K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => (ζ - z)⁻¹) atTop K := by sorry
