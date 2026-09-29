-- Prove2me | Theorems.Thm_SupportCompressionPoly_dominated_iff_subset_for_indicators
-- name    : SupportCompressionPoly.dominated_iff_subset_for_indicators
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:16:02.9742+00:00
-- url     : https://prove2.me/theorems/ee59a82f-0b42-4bb3-9338-bcd4da30873f
-- title:
--   For indicator finsupps, componentwise `≤` is equivalent to set containment.
-- statement:
--   For indicator finsupps, componentwise `≤` is equivalent to set containment.
--
--   ```lean
--   theorem SupportCompressionPoly.dominated_iff_subset_for_indicators    {I B : Finset (Fin n)} :
--       indicatorFinsupp I ≤ indicatorFinsupp B ↔ I ⊆ B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/SupportCompressionPoly.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/SupportCompressionPoly.lean#L92

-- Thm stub generated from Bridges/GraphTheory/SupportCompressionPoly.lean
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

theorem SupportCompressionPoly.dominated_iff_subset_for_indicators    {I B : Finset (Fin n)} :
    indicatorFinsupp I ≤ indicatorFinsupp B ↔ I ⊆ B := by sorry
