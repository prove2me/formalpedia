-- Prove2me | solution 1 for card_pow_ge_of_generates
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:04:25.793827+00:00
-- url     : https://prove2.me/submissions/6364c3c0-26a4-492a-ad75-15151a3b275b

-- Sol generated from Bridges/HilbertSpace/MatrixGroupGrowth.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_MatrixGroupGrowth
import Theorems.Thm_pow_strict_growth_of_generates
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


/-
**Theorem 2 (New elements in triple product).**
If `A` is a symmetric generating set with identity and `A^3` has not saturated,
then there exists an element in `A^3 ∖ A^2`. This is the combinatorial
primitive for Helfgott-style growth: before saturation, there is genuinely
new mass at each level.
-/

/-
**Theorem 3 (Cayley vertex expansion from product growth).**
If `S` is a generator set with identity and the product `A * S` is
at least `δ` larger than `A`, then the vertex boundary of `A` in the Cayley
graph `Cay(G, S)` has at least `δ` elements.

This bridges algebraic product-set growth to graph-theoretic expansion,
opening a path from Helfgott-style growth to verified expander constructions.
-/

/-
**Corollary: Triple-product growth implies Cayley expansion.**
Combining the strict growth theorem with the expansion bridge: before
saturation, a symmetric generating set always produces new boundary vertices
in the Cayley graph.
-/

/-! ## Section 5: Growth Rate Lower Bound -/

/-
**Theorem 4 (Quantitative growth rate lower bound).**
Before saturation, each power adds at least one element. Combined with
the total size bound, this gives `|A^n| ≥ min(|A| + n - 1, |G|)`.
-/

/-! ## Section 6: Escape Index Properties -/

/-
The escape index is well-defined for generating sets: if `A` generates `G`
and `H ⊊ univ`, then eventually some power escapes `H`.
-/

/-! ## Section 7: Conjectures -/


theorem solution    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G)
    (h1 : (1 : G) ∈ A)
    (hsym : ∀ a ∈ A, a⁻¹ ∈ A)
    (hgen : Subgroup.closure (↑A : Set G) = ⊤)
    (n : ℕ) (hn : 0 < n) :
    (A ^ n).card ≥ min (A.card + n - 1) (Fintype.card G) := by
      rcases n with ( _ | _ | n ) <;> simp_all +decide;
      induction' n with n ih;
      · by_cases h : A ^ 2 = Finset.univ <;> simp_all +decide [ pow_succ ];
        have := pow_strict_growth_of_generates A h1 hsym hgen 1 Nat.one_pos;
        simp_all +decide [ pow_succ' ];
        exact Or.inl ( this ( by rintro rfl; exact h ( by simp +decide ) ) );
      · by_cases h : A ^ ( n + 1 + 1 ) = Finset.univ;
        · simp_all +decide [ pow_succ, mul_assoc ];
          rw [ show ( Finset.univ : Finset G ) * A = Finset.univ from Finset.eq_univ_of_forall fun x => by simpa using Finset.mem_mul.2 ⟨ x * ( 1 : G ) ⁻¹, by aesop ⟩ ] ; simp +decide;
        · have h_card : (A ^ (n + 1 + 1)).card + 1 ≤ (A ^ (n + 1 + 1 + 1)).card := by
            apply pow_strict_growth_of_generates A h1 hsym hgen (n + 2) (by linarith) h;
          omega
