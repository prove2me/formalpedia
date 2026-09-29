-- Prove2me | solution 1 for ToricCode.toric_homologyRank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:55:27.369265+00:00
-- url     : https://prove2.me/submissions/2213bfcb-d641-4953-90b8-dbe371c5b154

-- Sol generated from Geometry/ToricCode/Homology.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_finrank_boundaries
import Theorems.Thm_ToricCode_finrank_cycles
import Theorems.Thm_ToricCode_one_le_mul
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



/-! ### Rank computations -/











open ToricCode in
theorem solution: homologyRank M N = 2 := by
  rw [homologyRank, finrank_cycles, finrank_boundaries]
  have := one_le_mul M N
  omega
