-- Prove2me | Theorems.Thm_CertificateCompressionExchange_multiaffine_le_iff_support_subset
-- name    : CertificateCompressionExchange.multiaffine_le_iff_support_subset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:39:29.245687+00:00
-- url     : https://prove2.me/theorems/4bac5f6b-39a9-40df-9ae1-d2c46a0c0f3d
-- title:
--   For multiaffine finsupps, domination is equivalent to support containment.
-- statement:
--   For multiaffine finsupps, domination is equivalent to support containment.
--
--   ```lean
--   theorem CertificateCompressionExchange.multiaffine_le_iff_support_subset{n : ℕ}
--       (α β : Fin n →₀ ℕ) (hα : IsMultiaffine α) (hβ : IsMultiaffine β) :
--       α ≤ β ↔ finsuppSupp α ⊆ finsuppSupp β := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/CertificateCompressionExchange.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/CertificateCompressionExchange.lean#L79

-- Thm stub generated from Bridges/GraphTheory/CertificateCompressionExchange.lean
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

theorem CertificateCompressionExchange.multiaffine_le_iff_support_subset{n : ℕ}
    (α β : Fin n →₀ ℕ) (hα : IsMultiaffine α) (hβ : IsMultiaffine β) :
    α ≤ β ↔ finsuppSupp α ⊆ finsuppSupp β := by sorry
