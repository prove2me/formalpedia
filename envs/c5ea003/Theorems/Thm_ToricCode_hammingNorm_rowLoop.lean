-- Prove2me | Theorems.Thm_ToricCode_hammingNorm_rowLoop
-- name    : ToricCode.hammingNorm_rowLoop
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:32:55.889048+00:00
-- url     : https://prove2.me/theorems/6bd5b2d3-838e-40fd-baf9-f3acf5ab6d7a
-- title:
--   A row loop has weight exactly `M`.
-- statement:
--   A row loop has weight exactly `M`.
--
--   ```lean
--   theorem ToricCode.hammingNorm_rowLoop(y : ZMod N) : hammingNorm (rowLoop M N y) = M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Rigidity.lean#L90

-- Thm stub generated from Geometry/ToricCode/Rigidity.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
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

theorem ToricCode.hammingNorm_rowLoop(y : ZMod N) : hammingNorm (rowLoop M N y) = M := by sorry
