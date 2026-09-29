-- Prove2me | solution 1 for SupportCompressionPoly.dominated_iff_subset_for_indicators
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:57:44.268649+00:00
-- url     : https://prove2.me/submissions/b61a8195-348b-478f-94c9-6ee0af5d7a72

-- Sol generated from Bridges/GraphTheory/SupportCompressionPoly.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_SupportCompressionPoly
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Polynomial-Level Support Compression for Multiaffine Polynomials

This file establishes the polynomial-algebraic foundation for support-compressed
Lorentzian recognition. The core result is that for multiaffine homogeneous
polynomials with positive coefficients, derivative survival is determined
entirely by support geometry—specifically, by subset containment between
the derivative's multiindex support and the polynomial's monomial supports.

## Core Mathematical Vision

For a matroid M of rank r on [n], the basis generating polynomial B_M is
homogeneous of degree r, multiaffine, and its support consists of basis
indicator vectors. The derivative ∂^α B_M is nonzero iff supp(α) is an
independent set of M. Thus nonzero quadratic leaves (where |α| = r-2)
are in bijection with independent (r-2)-sets.

This converts Lorentzian recognition from a symbolic algebra problem into
a combinatorial counting problem on the independent-set complex.

## Main Results

* `derivative_nonzero_iff_dominated_support` — Algebraic domination ↔ subset containment
* `derivative_survival_iff_independent` — Derivative survival = independent set membership
* `numberOfQuadraticLeaves_uniformMatroid` — Closed form C(n, r-2) for uniform matroids
* `supportCompressedLeafCount_le_active_choose` — Upper bound by active variables
* `independentSetsOfSize_hereditary` — Downward closure (matroid independence axiom)
* `independentSetsOfSize_singleton` — Single-basis exact count

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open Finset BigOperators Finsupp

noncomputable section

open SupportCompressionPoly

variable {n : ℕ}

/-! ## Multiaffine Exponents -/


/-! ## Indicator Exponents from Finsets -/





/-! ## Indicator Finsupp Domination ↔ Subset Containment -/



/-! ## Theorem 1: Exact Support Criterion -/



/-! ## Independent Sets from Basis Families -/







/-! ## Theorem 3: Uniform Matroid -/





/-! ## Theorem 4: Support Compression Upper Bound -/




/-! ## Verified Algorithm -/





/-! ## Structural Properties -/






/-! ## Derivative Survival = Independent Set Membership

The complete reduction from polynomial derivative survival to matroid
independent-set membership. -/




open SupportCompressionPoly in
theorem solution    {I B : Finset (Fin n)} :
    indicatorFinsupp I ≤ indicatorFinsupp B ↔ I ⊆ B := by
  constructor
  · intro h i hi
    have := h i
    simp only [indicatorFinsupp, Finsupp.coe_mk, if_pos hi] at this
    by_contra h'
    simp only [if_neg h'] at this
    omega
  · intro h i
    simp only [indicatorFinsupp, Finsupp.coe_mk]
    split
    · next hi => simp [if_pos (h hi)]
    · omega
