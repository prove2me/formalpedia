-- Prove2me | Theorems.Thm_exists_polynomial_separator_of_isCompact_nonempty_convex
-- name    : exists_polynomial_separator_of_isCompact_nonempty_convex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:29:48.881586+00:00
-- url     : https://prove2.me/theorems/b6b43668-e71a-408f-ae43-11fd14fab0d5
-- title:
--   exists polynomial separator of is Compact nonempty convex: exists polynomial separator of is Compact nonempty convex
-- statement:
--   A point outside a nonempty compact convex planar set can be separated in
--   modulus by an affine complex polynomial: the polynomial takes value one at
--   the exterior point and has norm uniformly bounded by some `r < 1` on the
--   set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRunge.lean#L137-L155
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRunge.lean#L137-L155

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_Operator_Crouzeix_ConvexRunge
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Topology

theorem exists_polynomial_separator_of_isCompact_nonempty_convex
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (hconvex : Convex ℝ K) {ζ : ℂ} (hζ : ζ ∉ K) :
    ∃ (p : Polynomial ℂ) (r : ℝ),
      0 ≤ r ∧ r < 1 ∧ Polynomial.eval ζ p = 1 ∧
        ∀ z ∈ K, ‖Polynomial.eval z p‖ ≤ r := by sorry
