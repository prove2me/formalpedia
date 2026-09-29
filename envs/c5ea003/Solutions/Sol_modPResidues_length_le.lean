-- Prove2me | solution 1 for modPResidues_length_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:40:47.451132+00:00
-- url     : https://prove2.me/submissions/9e7fe23b-e7f2-4098-957c-7c4f3ab39bab

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


theorem solution(lengths : List ℕ) (p : ℕ) (hp : 0 < p) :
    (modPResidues lengths p).length ≤ p := by
  -- The list of residues is a subset of {0, 1, ..., p-1}, and thus the length of the list after removing duplicates is at most p.
  have h_subset : (List.map (fun x => x % p) lengths).eraseDups.toFinset ⊆ Finset.range p := by
    intro x hx
    generalize_proofs at *; (
    have h_subset : ∀ x ∈ (lengths.map (fun x => x % p)).eraseDups, x < p := by
      intros x hx; exact (by
      have h_subset : ∀ x ∈ (lengths.map (fun x => x % p)).eraseDups, x ∈ List.map (fun x => x % p) lengths := by
        induction' ( List.map ( fun x => x % p ) lengths ) using List.reverseRecOn with x xs ih <;> simp_all +decide [ List.eraseDups_append ];
        simp_all +decide [ List.removeAll ];
        grind
      generalize_proofs at *; (
      exact List.mem_map.mp ( h_subset x hx ) |> fun ⟨ y, hy, hy' ⟩ => hy'.symm ▸ Nat.mod_lt _ hp));
    generalize_proofs at *; (
    exact Finset.mem_range.mpr ( h_subset x ( List.mem_toFinset.mp hx ) )))
  generalize_proofs at *; (
  convert Finset.card_le_card h_subset using 1
  generalize_proofs at *; (
  rw [ List.toFinset_card_of_nodup ] ; unfold modPResidues ; aesop;
  -- The eraseDupsBy loop preserves the nodup property.
  have h_eraseDupsBy_nodup : ∀ (l : List ℕ) (acc : List ℕ), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
    intros l acc hacc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
    cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide [ List.eraseDupsBy.loop ] ; aesop;
  generalize_proofs at *; (
  exact h_eraseDupsBy_nodup _ _ ( by simp +decide )));
  norm_num)
