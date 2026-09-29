-- Prove2me | Definitions.Def_Geometry_ErdosSzekeres_CupCapBound
-- name    : Geometry_ErdosSzekeres_CupCapBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:12:52.906545+00:00
-- url     : https://prove2.me/theorems/a512b6e9-c62c-4f03-aaa0-eaba80bb4e7e
-- title:
--   Aether Catalog definitions — Geometry_ErdosSzekeres_CupCapBound
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ErdosSzekeres.CupCapBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ErdosSzekeres/CupCapBound.lean by skeleton subtraction
import Mathlib
/-
# Cup-Cap Inductive Theory and ES Upper Bound

This file develops the combinatorial core of the Erdős–Szekeres cup-cap theorem:
the function CC(j,k) = C(j+k-4, j-2) + 1 satisfying the Pascal recurrence
CC(j,k) = CC(j-1,k) + CC(j,k-1) - 1, with base cases CC(2,k) = CC(j,2) = 2.

We introduce a novel **convex layer decomposition** (onion peeling) structure
that provides a quantitative measure of geometric complexity beyond the binary
notion of convex position.

## Main results

- `CupCapNumber`: CC(j,k) = C(j+k-4, j-2) + 1
- `cupCapNumber_base_left` / `cupCapNumber_base_right`: CC(2,k) = CC(j,2) = 2
- `cupCapNumber_recurrence`: CC(j,k) = CC(j-1,k) + CC(j,k-1) - 1 for j,k ≥ 3
- `cupCapNumber_symmetric`: CC(j,k) = CC(k,j) via Vandermonde symmetry
- `ConvexLayerDecomposition`: Novel structure for onion peeling
- `layers_le_points`: Each decomposition has ≤ m layers (by surjection argument)
- `cup_mono` / `cap_mono`: Size monotonicity for cups and caps
- `cup_iff_cap_reflect`: Duality via y-reflection
- `three_point_cup_or_cap`: Any 3 general-position points form a cup or cap
- `orient_cup_extend` / `orient_cap_extend`: Orientation transitivity
-/

open Finset Nat Function BigOperators

namespace HappyEnd

/-! ## The Cup-Cap Number -/

/-- The Cup-Cap number CC(j,k) is the threshold guaranteeing a j-cup or k-cap
among points in general position. The Erdős–Szekeres cup-cap theorem proves
this equals C(j+k-4, j-2) + 1.

For j < 2 or k < 2, we set CC = 0 (degenerate case). -/
def CupCapNumber (j k : ℕ) : ℕ :=
  if j < 2 ∨ k < 2 then 0
  else Nat.choose (j + k - 4) (j - 2) + 1

/-! ## Base Cases -/



/-! ## The Recurrence via Pascal's Rule -/


/-! ## Symmetry -/


/-! ## Specific Values -/




/-! ## The ES Upper Bound Formula -/


/-! ## Geometric Definitions -/

/-- The orientation (signed area × 2) of three points in the plane.
Positive = counterclockwise, negative = clockwise, zero = collinear. -/
def orient (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- General position: no three collinear. -/
def GeneralPosition {m : ℕ} (p : Fin m → ℝ × ℝ) : Prop :=
  ∀ i j k : Fin m, i ≠ j → j ≠ k → i ≠ k → orient (p i) (p j) (p k) ≠ 0


/-- A cup of size k: a strictly increasing index subsequence where
consecutive triples have positive orientation (concave up). -/
def HasCup {m : ℕ} (p : Fin m → ℝ × ℝ) (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin m, StrictMono f ∧
    (∀ (a : ℕ) (ha : a + 2 < k),
      orient (p (f ⟨a, by omega⟩)) (p (f ⟨a + 1, by omega⟩)) (p (f ⟨a + 2, by omega⟩)) > 0)

/-- A cap of size k: a strictly increasing index subsequence where
consecutive triples have negative orientation (concave down). -/
def HasCap {m : ℕ} (p : Fin m → ℝ × ℝ) (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin m, StrictMono f ∧
    (∀ (a : ℕ) (ha : a + 2 < k),
      orient (p (f ⟨a, by omega⟩)) (p (f ⟨a + 1, by omega⟩)) (p (f ⟨a + 2, by omega⟩)) < 0)

/-! ## Cup and Cap Monotonicity -/



/-! ## Orientation Algebraic Properties -/






/-! ## Orientation Transitivity -/



/-! ## Cup-Cap Duality via Reflection -/



/-! ## Structural Lemma: Three-Point Dichotomy -/


/-! ## Convex Layer Decomposition (Novel Definition) -/

/-- A **convex layer decomposition** (also known as onion peeling) of a
planar point set partitions the m points into nested convex layers.

Geometrically: the outermost layer (index 0) is the convex hull boundary,
the next layer (index 1) is the hull of the remaining points, and so on.
This provides a hierarchical measure of geometric complexity that refines
the binary notion of "in convex position" into a spectrum.

**Connection to the Happy End Problem**: The layer depth provides a lower
bound on how many convex polygons can be "peeled" from the configuration.
Deeper configurations require more points to guarantee large convex subsets,
linking layer theory to Erdős–Szekeres bounds.

**Connection to partial order theory**: Via the Dilworth-ES bridge, layer
depth corresponds to the width of the associated partial order — the
maximum antichain size in the order defined by comparing both index and value. -/
structure ConvexLayerDecomposition (m : ℕ) where
  /-- Number of convex layers -/
  layers : ℕ
  /-- Layer count is positive -/
  layers_pos : 0 < layers
  /-- Assignment of each point to a layer (0 = outermost hull) -/
  assignment : Fin m → Fin layers
  /-- Each layer is nonempty -/
  layer_nonempty : ∀ l : Fin layers, ∃ i : Fin m, assignment i = l




/-! ## The Cup-Cap Theorem Statement -/


/-! ## Growth Bounds -/


/-
CC(j,k) ≥ j when k ≥ j and j ≥ 2. Note: CC(j,2) = 2 for all j,
so the bound j ≤ CC(j,k) requires k ≥ j (or at least k ≥ 3 for j ≥ 3).
-/

/-! ## Conjecture: Cup-Cap Tightness -/


end HappyEnd


