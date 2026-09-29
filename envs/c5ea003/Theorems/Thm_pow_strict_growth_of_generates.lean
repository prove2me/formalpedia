-- Prove2me | Theorems.Thm_pow_strict_growth_of_generates
-- name    : pow_strict_growth_of_generates
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:29:37.835552+00:00
-- url     : https://prove2.me/theorems/b9077666-3c06-464e-8419-145c2637ee84
-- title:
--   Pow strict growth of generates
-- statement:
--   Formal statement of `pow_strict_growth_of_generates` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem pow_strict_growth_of_generates    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
--       (A : Finset G)
--       (h1 : (1 : G) ∈ A)
--       (hsym : ∀ a ∈ A, a⁻¹ ∈ A)
--       (hgen : Subgroup.closure (↑A : Set G) = ⊤)
--       (n : ℕ) (hn : 0 < n)
--       (hproper : A ^ n ≠ Finset.univ) :
--       (A ^ n).card < (A ^ (n + 1)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HilbertSpace/MatrixGroupGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HilbertSpace/MatrixGroupGrowth.lean#L203

-- Thm stub generated from Bridges/HilbertSpace/MatrixGroupGrowth.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_MatrixGroupGrowth
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quantitative Growth Bounds for Product Sets in Finite Groups

This file develops the first formal foundations for quantitative growth bounds
of product sets in finite groups, targeting the Helfgott paradigm for matrix
groups over finite fields. The central results establish that symmetric
generating sets must exhibit strict growth at every step before saturation,
and connect this algebraic growth to Cayley graph expansion.

## Main definitions

* `growthProfile`: The discrete derivative of product-set cardinalities.
* `escapeIndex`: The first power at which a set escapes a target region.
* `vertexBoundary`: The set of new vertices reached by one generator step.
* `HasDistinctEigenlines`: A matrix has two linearly independent eigenvectors
  with distinct eigenvalues.
* `PreservesEigenlinePair`: A matrix preserves the eigenlines of another.

## Main results

* `pow_strict_growth_of_generates`: Before saturation, every power strictly
  grows: if `A^n ≠ univ`, then `|A^(n+1)| > |A^n|`.
* `exists_new_element_in_triple_product`: If `A^3 ≠ univ`, there exists an
  element in `A^3 \ A^2`.
* `cayley_vertex_expansion_of_growth`: Product-set growth implies Cayley
  graph vertex expansion.

## References

* Helfgott, H.A. (2008). Growth and generation in `SL_2(ℤ/pℤ)`.
* Tao, T. (2015). Expansion in finite simple groups of Lie type.
* Breuillard, Green, Tao (2012). The structure of approximate groups.
-/


open Finset Pointwise

/-! ## Section 1: Core Definitions -/




/-! ## Section 2: Eigenline Definitions for GL(2) -/



/-! ## Section 3: Key Lemmas -/

/-
If `A^n = A^(n+1)` and `1 ∈ A`, then `A^n = A^(n+k)` for all `k`.
-/

/-
If `A = A⁻¹` and `1 ∈ A` and `A^n` is stable (A^n = A^(n+1)),
then `A^n` is closed under group multiplication.
-/

/-
If `A = A⁻¹`, then `(A^n)⁻¹ = A^n`.
-/

/-
If `A = A⁻¹`, `1 ∈ A`, and `A^n = A^(n+1)` with `n ≥ 1`, then `A^n`
contains a subgroup that contains `A`.
-/

/-
If `A` generates `G` and `A^n` is closed under multiplication and
inversion and contains `A`, then `A^n = univ`.
-/

/-! ## Section 4: Main Theorems -/

/-
**Theorem 1 (Strict growth before saturation).**
If `A` is a symmetric generating set containing the identity in a finite group,
and `A^n` has not yet saturated to the full group, then `A^(n+1)` is strictly
larger than `A^n`.

This is the fundamental rigidity principle: product powers of generating sets
cannot stall before reaching the full group. The proof proceeds by showing that
stabilization would force `A^n` to be a subgroup, which must be all of `G`
since `A` generates.
-/

theorem pow_strict_growth_of_generates    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G)
    (h1 : (1 : G) ∈ A)
    (hsym : ∀ a ∈ A, a⁻¹ ∈ A)
    (hgen : Subgroup.closure (↑A : Set G) = ⊤)
    (n : ℕ) (hn : 0 < n)
    (hproper : A ^ n ≠ Finset.univ) :
    (A ^ n).card < (A ^ (n + 1)).card := by sorry
