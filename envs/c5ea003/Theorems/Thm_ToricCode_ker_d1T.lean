-- Prove2me | Theorems.Thm_ToricCode_ker_d1T
-- name    : ToricCode.ker_d1T
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:12:43.902429+00:00
-- url     : https://prove2.me/theorems/ec3d3ec6-5902-4e98-9834-53ee9aadd8c1
-- title:
--   A `0`-cochain is a cocycle iff it is constant: the vertex graph of the torus
-- statement:
--   A `0`-cochain is a cocycle iff it is constant: the vertex graph of the torus
--   is connected.
--
--   ```lean
--   theorem ToricCode.ker_d1T:
--       LinearMap.ker ((d1 M N)ᵀ).mulVecLin = F2 ∙ (fun _ => 1 : Vert M N → F2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Homology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Homology.lean#L42

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

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]





/-! ### The two connectivity lemmas -/

theorem ToricCode.ker_d1T:
    LinearMap.ker ((d1 M N)ᵀ).mulVecLin = F2 ∙ (fun _ => 1 : Vert M N → F2) := by sorry
