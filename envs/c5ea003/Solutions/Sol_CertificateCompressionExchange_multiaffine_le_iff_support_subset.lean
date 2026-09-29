-- Prove2me | solution 1 for CertificateCompressionExchange.multiaffine_le_iff_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:00.129758+00:00
-- url     : https://prove2.me/submissions/52774a33-691b-438d-8c99-4cd52fea36e4

-- Sol generated from Bridges/GraphTheory/CertificateCompressionExchange.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_CertificateCompressionExchange
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Certificate Compression by Exchange Geometry

This file develops the theory of **certificate compression for Lorentzian
recognition** of matroid basis generating polynomials. The central insight is
that the recursion tree for recognizing Lorentzian polynomials collapses for
matroid basis polynomials because nonzero quadratic derivative leaves are in
bijection with independent sets — a consequence of multiaffine support geometry.

## Core Mathematical Statement

For a rank-r matroid M on ground set [n], the basis generating polynomial
  B_M(x₁,…,xₙ) = Σ_{B ∈ bases(M)} ∏_{i ∈ B} xᵢ
has the property that the iterated partial derivative ∂^α B_M is nonzero
if and only if supp(α) is an independent set of M. Hence the number of
nonzero quadratic leaves (|α| = r-2) equals the number of independent
(r-2)-sets.

## Main New Concepts

* `NonzeroQuadraticLeafSet` — The support-theoretic set of surviving derivative branches
* `basisIndicatorSupport` — Basis indicator vectors as finsupp support
* `NonzeroDerivProfile` — Which derivative indices survive at the multiindex level

## Main Theorems

* `derivative_survival_iff_independent` — Derivative survival = matroid independence
* `nonzeroQuadLeafSet_eq_indepSets` — Leaf set = independent set family
* `nonzeroQuadLeafSet_card_uniformMatroid` — Uniform matroid closed form C(n, r-2)
* `nonzeroQuadLeafSet_card_le_active` — Support compression upper bound
* `multiaffine_derivative_zero_of` — Monomial derivative vanishing criterion
* `indepCount_mono` — Monotonicity of independent set counts
* `countFromBases_eq_card` — Verified algorithm correctness

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open Finset BigOperators

noncomputable section

open CertificateCompressionExchange

/-! ## Part I: Multiaffine Finsupp Geometry -/











/-! ## Part II: Basis Family Abstraction -/








/-! ## Part III: New Concept — Nonzero Quadratic Leaf Set -/



/-! ## Part IV: New Concept — Basis Indicator Support -/




/-! ## Part V: New Concept — Nonzero Derivative Profile -/


/-! ## Part VI: Core Theorems -/





/-! ## Part VII: Uniform Matroid -/





/-! ## Part VIII: Support Compression Bound -/




/-! ## Part IX: Structural Properties -/




/-! ## Part X: Verified Algorithm -/





/-! ## Part XI: Monomial Derivative Vanishing -/



/-! ## Part XII: Exchange Geometry Connection -/



/-! ## Part XIII: Compression Ratio Analysis -/





open CertificateCompressionExchange in
theorem solution{n : ℕ}
    (α β : Fin n →₀ ℕ) (hα : IsMultiaffine α) (hβ : IsMultiaffine β) :
    α ≤ β ↔ finsuppSupp α ⊆ finsuppSupp β := by
  constructor
  · intro h i hi
    simp only [finsuppSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have := Finsupp.le_def.mp h i
    omega
  · intro h
    rw [Finsupp.le_def]
    intro i
    by_cases hi : α i = 0
    · omega
    · have : i ∈ finsuppSupp α := by simp [finsuppSupp, hi]
      have hmem := h this
      simp only [finsuppSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have h1 := hα i; have h2 := hβ i
      omega
