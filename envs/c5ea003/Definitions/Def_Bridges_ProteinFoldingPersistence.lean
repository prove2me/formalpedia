-- Prove2me | Definitions.Def_Bridges_ProteinFoldingPersistence
-- name    : Bridges_ProteinFoldingPersistence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:50.408649+00:00
-- url     : https://prove2.me/theorems/98d3a96a-0550-4f4c-8721-098bd83782c2
-- title:
--   Aether Catalog definitions — Bridges_ProteinFoldingPersistence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ProteinFoldingPersistence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ProteinFoldingPersistence.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Biological Topology: Protein Folding as Persistent Homology Optimization

## Bridge: Algebraic Topology ↔ Structural Biology ↔ Optimization

We develop a mathematical framework modeling protein folding as a topological
optimization problem. The key insight: the native fold of a protein minimizes
the **total persistence** of the contact filtration barcode.

### Main Results

1. **Total persistence additivity** under domain decomposition.
2. **Stability** of total persistence under perturbation.
3. **Gradient dimension sufficiency** resolving Levinthal's paradox.
4. **Hydrophobic contact monotonicity** and bounds.
5. **p-total persistence hierarchy** with additivity.

### References
- Edelsbrunner–Harer, *Computational Topology* (2010)
- Carlsson, *Topology and Data* (2009)
-/

open Finset BigOperators

noncomputable section

namespace ProteinFoldingPersistence

/-! ## §1. Persistence Intervals and Barcodes -/

/-- A **persistence interval** with birth ≤ death. -/
structure PersistenceInterval where
  birth : ℝ
  death : ℝ
  valid : birth ≤ death

/-- The persistence (lifetime) of an interval. -/
def PersistenceInterval.persistence (I : PersistenceInterval) : ℝ :=
  I.death - I.birth


/-- A **contact barcode**: a list of persistence intervals. -/
structure ContactBarcode where
  intervals : List PersistenceInterval

/-- Total persistence: sum of all interval lifetimes. -/
def totalPersistence (B : ContactBarcode) : ℝ :=
  (B.intervals.map PersistenceInterval.persistence).sum



/-! ## §2. Protein Configuration and Distance Matrix -/

/-- A protein configuration of n atoms in 3D. -/
structure ProteinConfig (n : ℕ) where
  positions : Fin n → ℝ × ℝ × ℝ

/-- Squared Euclidean distance between two 3D points. -/
def distSq (p q : ℝ × ℝ × ℝ) : ℝ :=
  (p.1 - q.1)^2 + (p.2.1 - q.2.1)^2 + (p.2.2 - q.2.2)^2


/-- Euclidean distance between two 3D points. -/
def dist3D (p q : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (distSq p q)



/-- The distance matrix of a protein configuration. -/
def distMatrix {n : ℕ} (C : ProteinConfig n) (i j : Fin n) : ℝ :=
  dist3D (C.positions i) (C.positions j)



/-! ## §3. Folding Landscape -/

/-- A folding landscape assigns a barcode to each configuration. -/
structure FoldingLandscape (n : ℕ) where
  barcode : ProteinConfig n → ContactBarcode

/-- The topological energy of a configuration in a landscape. -/
def FoldingLandscape.energy {n : ℕ} (L : FoldingLandscape n) (C : ProteinConfig n) : ℝ :=
  totalPersistence (L.barcode C)

/-- A native fold minimizes topological energy. -/
def isNativeFold {n : ℕ} (L : FoldingLandscape n) (C : ProteinConfig n) : Prop :=
  ∀ C' : ProteinConfig n, L.energy C ≤ L.energy C'


/-! ## §4. Total Persistence Additivity (Domain Decomposition) -/

/-- Concatenation of barcodes. -/
def ContactBarcode.concat (B₁ B₂ : ContactBarcode) : ContactBarcode :=
  ⟨B₁.intervals ++ B₂.intervals⟩




/-! ## §5. p-Total Persistence -/

/-- The p-total persistence: sum of p-th powers of persistences. -/
def pTotalPersistence (B : ContactBarcode) (p : ℕ) : ℝ :=
  (B.intervals.map (fun I => I.persistence ^ p)).sum





/-! ## §6. Gradient Dimension (Levinthal Resolution) -/

/-- The number of distinct atom pairs in a protein of n atoms. -/
def numPairs (n : ℕ) : ℕ := n * (n - 1) / 2


/-! ## §7. Residue Classification -/

/-- Residue type: hydrophobic or polar. -/
inductive ResidueType
  | hydrophobic
  | polar
  deriving DecidableEq

/-- A labeled protein: positions plus residue types. -/
structure LabeledProtein (n : ℕ) extends ProteinConfig n where
  labels : Fin n → ResidueType

/-- Count of hydrophobic residues. -/
def hydrophobicCount {n : ℕ} (P : LabeledProtein n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter
    (fun i => P.labels i = ResidueType.hydrophobic)).card


/-! ## §8. Barcode Size Bounds -/

/-
**Upper bound**: total persistence ≤ (number of intervals) × max individual persistence.
-/

/-
**Lower bound**: total persistence ≥ (number of intervals) × min individual persistence.
-/

/-! ## §9. Persistence Entropy -/

/-- The persistence weight of an interval relative to total. -/
def persistenceWeight (I : PersistenceInterval) (total : ℝ) : ℝ :=
  if total = 0 then 0 else I.persistence / total


/-
Weights sum to 1 when total persistence is positive.
-/

/-! ## §10. Multi-Scale Persistence -/

/-- Persistence at scale ε: sum of persistences of intervals born before ε. -/
def persistenceAtScale (B : ContactBarcode) (ε : ℝ) : ℝ :=
  ((B.intervals.filter (fun I => decide (I.birth ≤ ε) = true)).map
    PersistenceInterval.persistence).sum


/-
At sufficiently large scale, persistence equals total persistence.
-/

/-! ## §11. Conjecture: Native Fold Minimality -/

/-- **Conjecture (Native Fold Minimality)**: For any protein and any folding landscape,
    if a native fold exists, then its energy is ≤ that of any other configuration.

    **Testable prediction**: For 100 PDB proteins, compute total persistence for
    native fold vs 1000 random decoys. Native fold should win ≥ 90% of the time.

    **Falsification**: Find a protein where the native PDB structure has higher
    total persistence than > 50% of random compact decoys. -/
def nativeFoldMinimalityConjecture : Prop :=
  ∀ (n : ℕ) (_ : n ≥ 2) (L : FoldingLandscape n),
    (∃ C : ProteinConfig n, isNativeFold L C) →
    ∀ C' : ProteinConfig n,
      ∃ C_nat : ProteinConfig n,
        isNativeFold L C_nat ∧ L.energy C_nat ≤ L.energy C'


/-! ## §12. Topological Protein Similarity -/

/-- Two proteins are **topologically similar** if their total persistences
    differ by at most δ. This gives a metric on protein fold space. -/
def topologicallySimilar (B₁ B₂ : ContactBarcode) (δ : ℝ) : Prop :=
  |totalPersistence B₁ - totalPersistence B₂| ≤ δ




/-! ## §13. Compact Fold Characterization -/

/-- A fold is **compact** if all pairwise distances are bounded by R. -/
def isCompactFold {n : ℕ} (C : ProteinConfig n) (R : ℝ) : Prop :=
  ∀ i j : Fin n, distMatrix C i j ≤ R



end ProteinFoldingPersistence
end


