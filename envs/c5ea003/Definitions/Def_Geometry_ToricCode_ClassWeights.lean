-- Prove2me | Definitions.Def_Geometry_ToricCode_ClassWeights
-- name    : Geometry_ToricCode_ClassWeights
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:27:28.546992+00:00
-- url     : https://prove2.me/theorems/2a56e850-d540-47f0-9dab-ecaa2eca8092
-- title:
--   Aether Catalog definitions — Geometry_ToricCode_ClassWeights
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ToricCode.ClassWeights`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ToricCode/ClassWeights.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Homology
/-!
# Weights of individual logical classes: the diagonal class costs `M + N`

`ToricCode.toric_distance` says the *minimum* over all logical operators of the
`M × N` torus is `min M N`.  This file refines the analysis to individual
homology classes.

The winding pair `(hWind z 0, vWind z 0) ∈ 𝔽₂²` is a complete invariant of the
homology class (`ToricCode.boundaries_eq_trivialWinding`).  There are therefore
three nonzero classes: "horizontal", "vertical" and "diagonal".  The two cut
families — the `M` column cuts (horizontal edges) and the `N` row cuts (vertical
edges) — are *disjoint* as sets of qubits, so a cycle in the diagonal class must
meet all `M + N` of them:

* `sum_le_weight_of_both_windings` : weight `≥ M + N` for the diagonal class;
* `hammingNorm_loopHV` : the sum of the row loop and the column loop has weight
  exactly `M + N`;
* `diagonal_class_distance` : the minimal weight in the diagonal class is
  exactly `M + N`.

So the logical weight structure of the toric code is *not* uniform across
classes: the distance `min M N` is attained only on an "axis" class, and the
diagonal class is strictly more expensive.
-/

open Matrix

namespace ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]


/-- The diagonal logical operator: the row loop plus the column loop. -/
def loopHV : Edge M N → F2 := loopH M N + loopV M N






/-- Weights of the logical operators lying in the diagonal class. -/
def diagonalWeights : Set ℕ :=
  {w | ∃ z : Edge M N → F2, z ∈ cycles M N ∧ hWind M N z 0 ≠ 0 ∧ vWind M N z 0 ≠ 0 ∧
    hammingNorm z = w}



end ToricCode


