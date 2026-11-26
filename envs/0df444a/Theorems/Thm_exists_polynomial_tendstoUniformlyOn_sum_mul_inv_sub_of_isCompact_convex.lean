-- Prove2me | Theorems.Thm_exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
-- name    : exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:10.824603+00:00
-- url     : https://prove2.me/theorems/a8a0ebaa-72e0-427c-bece-6117fbca51f8
-- title:
--   exists polynomial tendsto Uniformly On sum mul inv sub of is Compact convex: exists polynomial tendsto Uniformly On sum mul inv sub of is Compact convex
-- statement:
--   A finite complex linear combination of Cauchy kernels with poles outside
--   a compact convex planar set is a compact-uniform limit of polynomials.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeFinite.lean#L45-L89
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeFinite.lean#L45-L89

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Definitions.Def_Operator_Crouzeix_ConvexRungeFinite
set_option autoImplicit false
open Complex Filter Set
open scoped Topology

theorem exists_polynomial_tendstoUniformlyOn_sum_mul_inv_sub_of_isCompact_convex
    {ι : Type*} (s : Finset ι) (coeff pole : ι → ℂ)
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hpole : ∀ i ∈ s, pole i ∉ K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => ∑ i ∈ s, coeff i * (pole i - z)⁻¹) atTop K := by sorry
