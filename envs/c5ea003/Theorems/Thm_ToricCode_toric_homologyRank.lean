-- Prove2me | Theorems.Thm_ToricCode_toric_homologyRank
-- name    : ToricCode.toric_homologyRank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:33:53.884526+00:00
-- url     : https://prove2.me/theorems/6221a42f-d95c-4b60-b5f5-f83a3c001089
-- title:
--   The `M × N` toric code encodes exactly two logical qubits.
-- statement:
--   **The `M × N` toric code encodes exactly two logical qubits.**
--   The first `𝔽₂`-homology of the square torus has rank `2`, matching the genus-one
--   answer `2g = 2` — but here it is derived from a genuine cellulation, not from an
--   abstract minimal CW model.
--
--   ```lean
--   theorem ToricCode.toric_homologyRank: homologyRank M N = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Homology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Homology.lean#L163

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

theorem ToricCode.toric_homologyRank: homologyRank M N = 2 := by sorry
