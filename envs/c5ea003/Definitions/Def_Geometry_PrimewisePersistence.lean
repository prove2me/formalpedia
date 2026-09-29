-- Prove2me | Definitions.Def_Geometry_PrimewisePersistence
-- name    : Geometry_PrimewisePersistence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:50:20.613986+00:00
-- url     : https://prove2.me/theorems/42e79be8-caa2-40ca-821f-ee7653040888
-- title:
--   Aether Catalog definitions — Geometry_PrimewisePersistence
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PrimewisePersistence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PrimewisePersistence.lean by skeleton subtraction
import Mathlib
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

/-- A persistence interval represents a topological feature born at time `birth`
    and dying at time `death`, with birth ≤ death. -/
structure PersistenceInterval where
  birth : ℕ
  death : ℕ
  valid : birth ≤ death
  deriving DecidableEq

namespace PersistenceInterval

/-- The lifetime (persistence) of an interval. -/
def lifetime (I : PersistenceInterval) : ℕ := I.death - I.birth

/-- An interval is alive at filtration parameter t. -/
def aliveAt (I : PersistenceInterval) (t : ℕ) : Prop :=
  I.birth ≤ t ∧ t < I.death

instance decAliveAt (I : PersistenceInterval) (t : ℕ) : Decidable (I.aliveAt t) :=
  inferInstanceAs (Decidable (_ ∧ _))





end PersistenceInterval

/-! ## Barcodes -/

/-- A barcode is a finite list of persistence intervals. -/
abbrev Barcode := List PersistenceInterval

namespace Barcode

/-- The Betti number at filtration parameter t: count of intervals alive at t. -/
def bettiAt (B : Barcode) (t : ℕ) : ℕ :=
  (B.filter (fun I => decide (I.aliveAt t))).length




end Barcode

/-! ## Rank Function -/

/-- The rank function β(s, t) counts intervals [b, d) with b ≤ s and t < d.
    This encodes the persistent Betti numbers. -/
def rankFunction (B : Barcode) (s t : ℕ) : ℕ :=
  (B.filter (fun I => decide (I.birth ≤ s ∧ t < I.death))).length

/-
The rank function is monotone decreasing in the second argument.
-/

/-
The rank function is monotone increasing in the first argument.
-/




/-! ## Interval Matching Cost (Bottleneck Distance) -/

/-- The cost of matching two persistence intervals:
    max of |birth₁ - birth₂| and |death₁ - death₂|. -/
def intervalMatchCost (I J : PersistenceInterval) : ℕ :=
  max (Int.natAbs ((I.birth : ℤ) - J.birth)) (Int.natAbs ((I.death : ℤ) - J.death))



/-
Triangle inequality for interval match cost.
-/

/-! ## Primewise Barcodes -/



/-! ## Prime Density -/



/-! ## Mod-p Filtration -/

/-- Given a list of natural numbers and a prime p, compute the sorted list
    of distinct residues mod p. This determines the filtration structure. -/
def modPResidues (lengths : List ℕ) (p : ℕ) : List ℕ :=
  (lengths.map (· % p)).eraseDups

/-
The number of distinct residues mod p is at most p.
-/

/-
Distinct lists can be separated by their mod-p residue structure.
-/

/-! ## Sunada-Type Isospectral Pairs -/

/-- A Sunada configuration: two subgroups of the same size with identical
    conjugacy class intersection counts (isospectrality condition). -/
structure SunadaConfig where
  numClasses : ℕ
  classCount₁ : Fin numClasses → ℕ
  classCount₂ : Fin numClasses → ℕ
  isospectral : classCount₁ = classCount₂


/-! ## Euler Characteristic via Barcodes -/

/-- For an alternating sum of Betti numbers, barcodes give
    the Euler characteristic at each filtration level. -/
def eulerCharAt (evens odds : Barcode) (t : ℕ) : ℤ :=
  (evens.bettiAt t : ℤ) - (odds.bettiAt t : ℤ)



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

/-- **Conjecture (Testable)**: For any two distinct lists of natural numbers
    with the same multiset, the set of primes that separate their
    mod-p residue patterns has density 1.

    This is computationally testable: given specific isospectral pairs,
    compute mod-p residues for p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}
    and check if barcodes differ. The conjecture predicts that only
    finitely many primes should fail to separate. -/
def conjecture_density_one_separation : Prop :=
  ∀ (a b : List ℕ),
    a.length = b.length →
    List.Perm a b →
    a ≠ b →
    ∃ (S : Set ℕ),
      Set.Finite S ∧
      ∀ p, Nat.Prime p → p ∉ S → a.map (· % p) ≠ b.map (· % p)

/-
The conjecture follows from the large prime preservation theorem:
    the exceptional set consists of primes up to the maximum element.
-/

end


