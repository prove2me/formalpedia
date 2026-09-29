-- Prove2me | Definitions.Def_Bridges_GraphTheory_SupportCompressionPoly
-- name    : Bridges_GraphTheory_SupportCompressionPoly
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:45.074089+00:00
-- url     : https://prove2.me/theorems/43e18f42-aadb-4ff4-aabc-e5c3cc41df5a
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_SupportCompressionPoly
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.SupportCompressionPoly`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/SupportCompressionPoly.lean by skeleton subtraction
import Mathlib
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

namespace SupportCompressionPoly

variable {n : ℕ}

/-! ## Multiaffine Exponents -/

/-- A finitely-supported function `β : Fin n →₀ ℕ` is multiaffine if every
component is at most 1. -/
def IsMultiaffineExponent (β : Fin n →₀ ℕ) : Prop :=
  ∀ i : Fin n, β i ≤ 1

/-! ## Indicator Exponents from Finsets -/

/-- Convert a `Finset (Fin n)` to a `Fin n →₀ ℕ` indicator vector (0/1-valued). -/
def indicatorFinsupp (S : Finset (Fin n)) : Fin n →₀ ℕ where
  support := S
  toFun i := if i ∈ S then 1 else 0
  mem_support_toFun i := by simp




/-! ## Indicator Finsupp Domination ↔ Subset Containment -/



/-! ## Theorem 1: Exact Support Criterion -/



/-! ## Independent Sets from Basis Families -/

/-- The set of `k`-element subsets of `Fin n` that are contained in some member
of a family `bases`. -/
def independentSetsOfSize (bases : Finset (Finset (Fin n)))
    (k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard k).filter (fun I => ∃ B ∈ bases, I ⊆ B)

/-- Active variables: those appearing in at least one basis. -/
def activeVariables (bases : Finset (Finset (Fin n))) : Finset (Fin n) :=
  bases.biUnion id

/-- Active variable count. -/
def activeVariableCount (bases : Finset (Finset (Fin n))) : ℕ :=
  (activeVariables bases).card




/-! ## Theorem 3: Uniform Matroid -/

/-- The uniform basis family: all `r`-element subsets of `Fin n`. -/
def uniformBases (n r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard r




/-! ## Theorem 4: Support Compression Upper Bound -/




/-! ## Verified Algorithm -/

/-- Count nonzero quadratic leaves from basis data without polynomial differentiation. -/
def countNonzeroQuadraticLeavesFromBases
    (bases : Finset (Finset (Fin n))) (r : ℕ) : ℕ :=
  (independentSetsOfSize bases (r - 2)).card




/-! ## Structural Properties -/






/-! ## Derivative Survival = Independent Set Membership

The complete reduction from polynomial derivative survival to matroid
independent-set membership. -/



end SupportCompressionPoly


