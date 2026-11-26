-- Prove2me | Theorems.Thm_exists_polynomial_tendstoUniformlyOn_of_tendstoUniformlyOn_cauchyKernel_finset
-- name    : exists_polynomial_tendstoUniformlyOn_of_tendstoUniformlyOn_cauchyKernel_finset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:38:20.773624+00:00
-- url     : https://prove2.me/theorems/32003e95-32bb-5f80-a8ea-60f2fb2a5f9a
-- title:
--   exists polynomial tendsto Uniformly On of tendsto Uniformly On cauchy Kernel finset: exists polynomial tendsto Uniformly On of tendsto Uniformly On cauchy Kernel finset
-- statement:
--   A compact-uniform limit of finite exterior Cauchy-kernel sums on a compact
--   convex planar set is itself a compact-uniform limit of polynomials.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeClosure.lean#L57-L73
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeClosure.lean#L57-L73

import Definitions.Def_Operator_Crouzeix_ConvexRungeFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_Operator_Crouzeix_ConvexRungeClosure
set_option autoImplicit false
open Filter Polynomial Set
open scoped Topology

theorem exists_polynomial_tendstoUniformlyOn_of_tendstoUniformlyOn_cauchyKernel_finset
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (poles : ℕ → Finset ℂ) (coeff : ℕ → ℂ → ℂ)
    (hpoles : ∀ n ζ, ζ ∈ poles n → ζ ∉ K) {f : ℂ → ℂ}
    (hlim : TendstoUniformlyOn
      (fun n z ↦ ∑ ζ ∈ poles n, coeff n ζ * (ζ - z)⁻¹)
      f atTop K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z ↦ Polynomial.eval z (q n))
        f atTop K := by sorry
