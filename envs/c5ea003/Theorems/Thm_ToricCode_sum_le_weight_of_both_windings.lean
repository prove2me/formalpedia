-- Prove2me | Theorems.Thm_ToricCode_sum_le_weight_of_both_windings
-- name    : ToricCode.sum_le_weight_of_both_windings
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:33:12.546876+00:00
-- url     : https://prove2.me/theorems/7d0de8af-9806-4d1f-b470-82dfbbbb28a7
-- title:
--   The diagonal logical class has weight at least `M + N`.
-- statement:
--   **The diagonal logical class has weight at least `M + N`.**  A cycle whose two
--   winding parities are both nonzero must meet each of the `M` column cuts and each
--   of the `N` row cuts, and these `M + N` cuts are pairwise disjoint sets of qubits.
--
--   ```lean
--   theorem ToricCode.sum_le_weight_of_both_windings{z : Edge M N → F2}
--       (hz : z ∈ cycles M N) (hh : hWind M N z 0 ≠ 0) (hv : vWind M N z 0 ≠ 0) :
--       M + N ≤ hammingNorm z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/ClassWeights.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/ClassWeights.lean#L32

-- Thm stub generated from Geometry/ToricCode/ClassWeights.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
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

-- open removed: section is not a namespace

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

theorem ToricCode.sum_le_weight_of_both_windings{z : Edge M N → F2}
    (hz : z ∈ cycles M N) (hh : hWind M N z 0 ≠ 0) (hv : vWind M N z 0 ≠ 0) :
    M + N ≤ hammingNorm z := by sorry
