-- Prove2me | Theorems.Thm_finite_agreement_primes
-- name    : finite_agreement_primes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:06:29.35667+00:00
-- url     : https://prove2.me/theorems/a1b09119-36e1-445d-bfe3-eb17c3228c54
-- title:
--   Finite agreement primes
-- statement:
--   Formal statement of `finite_agreement_primes` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem finite_agreement_primes    (a b : List ℕ)
--       (hlen : a.length = b.length) (hlen_pos : 0 < a.length)
--       (hdiff : ∃ i, ∃ hi : i < a.length,
--         a.get ⟨i, hi⟩ ≠ b.get ⟨i, by omega⟩) :
--       Set.Finite {p : ℕ | Nat.Prime p ∧ a.map (· % p) = b.map (· % p)} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PrimewisePersistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PrimewisePersistence.lean#L297

-- Thm stub generated from Geometry/PrimewisePersistence.lean
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

theorem finite_agreement_primes    (a b : List ℕ)
    (hlen : a.length = b.length) (hlen_pos : 0 < a.length)
    (hdiff : ∃ i, ∃ hi : i < a.length,
      a.get ⟨i, hi⟩ ≠ b.get ⟨i, by omega⟩) :
    Set.Finite {p : ℕ | Nat.Prime p ∧ a.map (· % p) = b.map (· % p)} := by sorry
