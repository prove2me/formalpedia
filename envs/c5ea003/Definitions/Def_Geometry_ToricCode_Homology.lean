-- Prove2me | Definitions.Def_Geometry_ToricCode_Homology
-- name    : Geometry_ToricCode_Homology
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:25:50.230896+00:00
-- url     : https://prove2.me/theorems/22552d26-27dc-4480-b1b2-3717718f355d
-- title:
--   Aether Catalog definitions — Geometry_ToricCode_Homology
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ToricCode.Homology`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ToricCode/Homology.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
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

namespace ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

/-- The `𝔽₂`-space of cellular one-cycles. -/
noncomputable def cycles : Submodule F2 (Edge M N → F2) := LinearMap.ker (d1 M N).mulVecLin

/-- The `𝔽₂`-space of cellular one-boundaries. -/
noncomputable def boundaries : Submodule F2 (Edge M N → F2) := LinearMap.range (d2 M N).mulVecLin


/-- First Betti number over `𝔽₂`. -/
noncomputable def homologyRank : ℕ :=
  Module.finrank F2 (cycles M N) - Module.finrank F2 (boundaries M N)

/-! ### The two connectivity lemmas -/



/-! ### Rank computations -/










end ToricCode


