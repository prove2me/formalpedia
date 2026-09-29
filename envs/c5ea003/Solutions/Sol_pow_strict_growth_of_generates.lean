-- Prove2me | solution 1 for pow_strict_growth_of_generates
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:01:31.830524+00:00
-- url     : https://prove2.me/submissions/5825a929-d988-4a78-a5a3-9bfd50b395b0

-- Sol generated from Bridges/HilbertSpace/MatrixGroupGrowth.lean
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
theorem pow_stabilize_of_eq
    {G : Type*} [Group G] [DecidableEq G]
    (A : Finset G) (h1 : (1 : G) ∈ A) (n : ℕ)
    (hstab : A ^ n = A ^ (n + 1)) :
    ∀ k : ℕ, A ^ n = A ^ (n + k) := by
      intro k;
      induction' k with k ih;
      · rfl;
      · convert congr_arg ( · * A ) ih using 1

/-
If `A = A⁻¹` and `1 ∈ A` and `A^n` is stable (A^n = A^(n+1)),
then `A^n` is closed under group multiplication.
-/
theorem pow_stable_mul_closed
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : (1 : G) ∈ A)
    (hsym : ∀ a ∈ A, a⁻¹ ∈ A)
    (n : ℕ) (hn : 0 < n)
    (hstab : A ^ n = A ^ (n + 1)) :
    ∀ x y : G, x ∈ A ^ n → y ∈ A ^ n → x * y ∈ A ^ n := by
      -- Since $A^n = A^{n+1}$, we have $A^n$ is close under multiplication.
      have h_closed : ∀ k : ℕ, A ^ n = A ^ (n + k) := by
        exact?;
      intro x y hx hy
      have hxy : x * y ∈ A ^ (n + n) := by
        rw [ pow_add ];
        exact Finset.mul_mem_mul hx hy;
      exact h_closed n ▸ hxy

/-
If `A = A⁻¹`, then `(A^n)⁻¹ = A^n`.
-/
theorem pow_inv_eq_of_inv
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G)
    (hsym : ∀ a ∈ A, a⁻¹ ∈ A)
    (n : ℕ) :
    (A ^ n)⁻¹ = A ^ n := by
      induction' n with n ih;
      · simp +decide;
      · simp +decide [ pow_succ, ih ];
        rw [ show A⁻¹ = A from _ ];
        · exact?;
        · ext x; simp +decide [ hsym ] ;
          exact ⟨ fun hx => by simpa using hsym _ hx, fun hx => hsym _ hx ⟩

/-
If `A = A⁻¹`, `1 ∈ A`, and `A^n = A^(n+1)` with `n ≥ 1`, then `A^n`
contains a subgroup that contains `A`.
-/
theorem closure_subset_pow_of_stable
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : (1 : G) ∈ A)
    (hsym : ∀ a ∈ A, a⁻¹ ∈ A)
    (n : ℕ) (hn : 0 < n)
    (hstab : A ^ n = A ^ (n + 1)) :
    (↑A : Set G) ⊆ ↑(A ^ n) ∧
    ∀ x y : G, x ∈ A ^ n → y ∈ A ^ n → x * y ∈ A ^ n ∧ x⁻¹ ∈ A ^ n := by
      refine' ⟨ _, fun x y hx hy => ⟨ pow_stable_mul_closed A h1 hsym n hn hstab x y hx hy, _ ⟩ ⟩;
      · refine' fun x hx => _;
        refine' Nat.le_induction _ _ n hn <;> intros <;> simp_all +decide [ pow_succ ];
        exact ⟨ x, by assumption, 1, h1, mul_one _ ⟩;
      · -- By definition of $A^n$, we know that $x⁻¹ ∈ (A^n)⁻¹$.
        have h_inv : x⁻¹ ∈ (A ^ n)⁻¹ := by
          exact?;
        rwa [ pow_inv_eq_of_inv A hsym ] at h_inv

/-
If `A` generates `G` and `A^n` is closed under multiplication and
inversion and contains `A`, then `A^n = univ`.
-/
theorem pow_eq_univ_of_generates_and_closed
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : (1 : G) ∈ A)
    (hgen : Subgroup.closure (↑A : Set G) = ⊤)
    (n : ℕ) (hn : 0 < n)
    (hsub : (↑A : Set G) ⊆ ↑(A ^ n))
    (hclosed : ∀ x y : G, x ∈ A ^ n → y ∈ A ^ n → x * y ∈ A ^ n)
    (hinv : ∀ x : G, x ∈ A ^ n → x⁻¹ ∈ A ^ n) :
    A ^ n = Finset.univ := by
      refine' Finset.eq_univ_of_forall _;
      intro x
      have hx : x ∈ Subgroup.closure (A : Set G) := by
        aesop;
      refine' Subgroup.closure_induction _ _ _ _ hx;
      · exact fun x hx => hsub hx;
      · exact hsub h1;
      · exact fun x y hx hy hx' hy' => hclosed x y hx' hy';
      · exact fun x hx hx' => hinv x hx'

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
    (n : ℕ) (hn : 0 < n)
    (hproper : A ^ n ≠ Finset.univ) :
    (A ^ n).card < (A ^ (n + 1)).card := by
      refine' Finset.card_lt_card _;
      contrapose! hproper;
      apply pow_eq_univ_of_generates_and_closed A h1 hgen n hn;
      · convert closure_subset_pow_of_stable A h1 hsym n hn _ |>.1;
        refine' le_antisymm _ _;
        · exact Finset.subset_iff.2 fun x hx => by rw [ pow_succ ] ; exact Finset.mem_mul.2 ⟨ x, hx, 1, h1, mul_one x ⟩ ;
        · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
          exact fun x hx => hproper ( fun x hx => Finset.mem_mul.mpr ⟨ x, hx, 1, h1, mul_one x ⟩ ) x hx;
      · convert pow_stable_mul_closed A h1 hsym n hn _;
        refine' le_antisymm _ _;
        · exact Finset.subset_iff.2 fun x hx => by rw [ pow_succ ] ; exact Finset.mem_mul.2 ⟨ x, hx, 1, h1, mul_one x ⟩ ;
        · simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
          exact fun x hx => hproper ( fun x hx => Finset.mem_mul.mpr ⟨ x, hx, 1, h1, mul_one x ⟩ ) x hx;
      · convert pow_inv_eq_of_inv A hsym n;
        simp +decide [ Finset.ext_iff ];
        exact ⟨ fun h x => ⟨ fun hx => by simpa using h _ hx, fun hx => h _ hx ⟩, fun h x hx => h _ |>.2 hx ⟩
