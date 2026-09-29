-- Prove2me | Theorems.Thm_ToricCode_no_vertical_edge_of_min_weight
-- name    : ToricCode.no_vertical_edge_of_min_weight
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:33:24.017513+00:00
-- url     : https://prove2.me/theorems/2cc4f9ca-01fb-472b-b149-324b150f5182
-- title:
--   **A minimum-weight logical operator of a strictly rectangular torus contains
-- statement:
--   **A minimum-weight logical operator of a strictly rectangular torus contains
--   no vertical edge.**
--
--   ```lean
--   theorem ToricCode.no_vertical_edge_of_min_weight(hMN : M < N) {z : Edge M N → F2}
--       (hz : z ∈ cycles M N) (hnb : z ∉ boundaries M N) (hw : hammingNorm z = M)
--       (x : ZMod M) (y : ZMod N) : z (true, (x, y)) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Rigidity.lean#L111

-- Thm stub generated from Geometry/ToricCode/Rigidity.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Homology
import Definitions.Def_Geometry_ToricCode_Rigidity
/-!
# Rigidity of minimum-weight logical operators

`ToricCode.toric_distance` computes the *value* `min M N` of the `Z`-distance.
This file classifies the *optimisers*: for a strictly rectangular torus
(`M < N`) a logical operator of the minimal weight `M` is **exactly** one of the
`N` horizontal row loops — no other chain achieves the distance.

* `rowLoop y` — all `M` horizontal edges of the row at height `y`;
* `rowLoop_is_logical` / `hammingNorm_rowLoop` — each row loop is a logical
  operator of weight `M`;
* `min_weight_logical_eq_rowLoop` — the converse, i.e. rigidity;
* `min_weight_logicals_card` — consequently the minimum-weight logical operators
  are in bijection with `ZMod N`: there are exactly `N` of them.

The proof is a counting rigidity argument.  A cycle with nonzero horizontal
winding meets each of the `M` disjoint column cuts, so weight `M` forces the
support to meet each cut *exactly once* and to contain **no vertical edge at
all**.  A purely horizontal cycle satisfies `z(false, u) = z(false, u - (1,0))`,
so its indicator is constant along each row; counting the support again then
forces exactly one row to be occupied.
-/

-- open removed: section is not a namespace

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]




variable {M N}








/-! ### Rigidity -/

theorem ToricCode.no_vertical_edge_of_min_weight(hMN : M < N) {z : Edge M N → F2}
    (hz : z ∈ cycles M N) (hnb : z ∉ boundaries M N) (hw : hammingNorm z = M)
    (x : ZMod M) (y : ZMod N) : z (true, (x, y)) = 0 := by sorry
