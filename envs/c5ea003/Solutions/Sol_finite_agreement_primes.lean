-- Prove2me | solution 1 for finite_agreement_primes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:40:11.030212+00:00
-- url     : https://prove2.me/submissions/9f2b554a-d636-42b2-bb6c-b305e0a97099

-- Sol generated from Geometry/PrimewisePersistence.lean
import Mathlib
import Definitions.Def_Geometry_PrimewisePersistence
/-
# Primewise Persistent Homology for Arithmetic Manifold Discrimination

This file develops the theory of prime-indexed persistence invariants
that can potentially distinguish isospectral but nonisometric arithmetic manifolds.

We define:
- `PersistenceInterval`: birth-death pairs with ordering
- `Barcode`: finite lists of persistence intervals
- `PrimewiseBarcode`: prime-indexed families of barcodes
- `BottleneckMatchCost`: matching cost for bottleneck distance

Key results:
- Triangle inequality for interval matching cost
- Rank function monotonicity in both arguments
- Betti number bounds and additivity
- Separating prime existence for distinct length lists
-/


open Finset Nat BigOperators

noncomputable section

/-! ## Persistence Intervals -/


open PersistenceInterval









/-! ## Barcodes -/


open Barcode






/-! ## Rank Function -/


/-
The rank function is monotone decreasing in the second argument.
-/

/-
The rank function is monotone increasing in the first argument.
-/




/-! ## Interval Matching Cost (Bottleneck Distance) -/




/-
Triangle inequality for interval match cost.
-/

/-! ## Primewise Barcodes -/



/-! ## Prime Density -/



/-! ## Mod-p Filtration -/


/-
The number of distinct residues mod p is at most p.
-/

/-
Distinct lists can be separated by their mod-p residue structure.
-/

/-! ## Sunada-Type Isospectral Pairs -/



/-! ## Euler Characteristic via Barcodes -/




/-! ## Key Theorem: Distinguishing via Residues -/

/-
**Core Separation Lemma**: If two natural number lists agree as multisets
    (same elements with same multiplicity) but differ in order,
    then for any prime p larger than all elements, the mod-p images
    preserve the ordering difference.

    This is the foundational result that makes primewise invariants
    potentially useful for geometric discrimination.
-/
theorem large_prime_preserves_order
    (a b : List ℕ) (M : ℕ)
    (hbound_a : ∀ x ∈ a, x ≤ M)
    (hbound_b : ∀ x ∈ b, x ≤ M)
    (p : ℕ) (hp : Nat.Prime p) (hp_large : M < p)
    (hdiff : a ≠ b) :
    a.map (· % p) ≠ b.map (· % p) := by
  convert hdiff using 1;
  · rw [ List.map_congr_left fun x hx => Nat.mod_eq_of_lt ( lt_of_le_of_lt ( hbound_a x hx ) hp_large ) ] ; aesop;
  · exact Eq.symm ( List.map_congr_left fun x hx => Nat.mod_eq_of_lt ( lt_of_le_of_lt ( hbound_b x hx ) hp_large ) ) ▸ by norm_num;

/-
**Agreement Bound**: The number of primes at which two bounded
    distinct lists have identical mod-p images is finite.
    Specifically, any agreement prime must divide some pairwise difference.
-/

/-! ## Main Conjecture -/


/-
The conjecture follows from the large prime preservation theorem:
    the exceptional set consists of primes up to the maximum element.
-/


theorem solution    (a b : List ℕ)
    (hlen : a.length = b.length) (hlen_pos : 0 < a.length)
    (hdiff : ∃ i, ∃ hi : i < a.length,
      a.get ⟨i, hi⟩ ≠ b.get ⟨i, by omega⟩) :
    Set.Finite {p : ℕ | Nat.Prime p ∧ a.map (· % p) = b.map (· % p)} := by
  -- Let $M = \max(\max �(a�), \max(b))$.
  set M := max (a.foldl max 0) (b.foldl max 0) with hM_def
  generalize_proofs at *; (
  -- By the large_prime_preserves_order theorem, any prime p > M separates the lists.
  have h_large_prime : ∀ p, Nat.Prime p → M < p → (a.map (· % p)) ≠ (b.map (· % p)) := by
    intro p hp hpM
    have h_bound_a : ∀ x ∈ a, x ≤ M := by
      intro x hx
      have h_foldl_max : x ≤ List.foldl max 0 a := by
        have h_foldl_max : ∀ {l : List ℕ}, x ∈ l → x ≤ List.foldl max 0 l := by
          intros l hl; induction' l using List.reverseRecOn with l IH <;> aesop;
        generalize_proofs at *; (exact h_foldl_max hx)
      generalize_proofs at *; (
      exact le_trans h_foldl_max ( le_max_left _ _ ))
    have h_bound_b : ∀ x ∈ b, x ≤ M := by
      -- By definition of $M$, we know that every element in $b$ is less than or equal to $M$.
      intros x hx
      have h_foldl_b : ∀ {l : List ℕ}, x ∈ l → x ≤ List.foldl max 0 l := by
        intros l hl; induction' l using List.reverseRecOn with l IH <;> aesop;
      generalize_proofs at *; (
      exact le_trans ( h_foldl_b hx ) ( le_max_right _ _ ))
    generalize_proofs at *; (
    apply large_prime_preserves_order a b M h_bound_a h_bound_b p hp hpM; aesop;)
  generalize_proofs at *; (
  exact Set.finite_iff_bddAbove.mpr ⟨ M, fun p hp => not_lt.1 fun contra => h_large_prime p hp.1 contra hp.2 ⟩))
