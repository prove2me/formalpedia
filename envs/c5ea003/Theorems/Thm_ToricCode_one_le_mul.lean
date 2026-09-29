-- Prove2me | Theorems.Thm_ToricCode_one_le_mul
-- name    : ToricCode.one_le_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:31:58.89998+00:00
-- url     : https://prove2.me/theorems/30d591c4-d60b-4e27-a969-e130f0c35669
-- title:
--   One le mul
-- statement:
--   Formal statement of `ToricCode.one_le_mul` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ToricCode.one_le_mul: 1 ≤ M * N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Homology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Homology.lean#L130

-- Thm stub generated from Geometry/ToricCode/Homology.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Homology
/-!
# First homology of the square torus: rank exactly two

We compute `dim_{𝔽₂} H₁ = dim ker d₁ - dim im d₂ = 2` for the `M × N` square
torus, for *every* `M, N ≥ 1`.

The computation avoids any explicit basis of the cycle space.  Instead:

* the kernel of the coboundary `d₁ᵀ` is the line of constant `0`-cochains
  (`ker_d1T`), because the vertex graph of the torus is connected;
* the kernel of `d₂` is the line of constant `2`-chains (`ker_d2`), because the
  dual graph is connected;
* hence `rank d₁ᵀ = MN - 1`, and `rank d₁ = rank d₁ᵀ` by the row-rank/column-rank
  theorem, so `dim ker d₁ = 2MN - (MN - 1) = MN + 1`;
* and `dim im d₂ = MN - 1`;
* subtracting gives `2`.
-/

-- open removed: section is not a namespace

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]





/-! ### The two connectivity lemmas -/



/-! ### Rank computations -/

theorem ToricCode.one_le_mul: 1 ≤ M * N := by sorry
