-- Prove2me | solution 1 for ToricCode.finrank_cycles
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:48:49.180306+00:00
-- url     : https://prove2.me/submissions/68739a49-0b08-476f-bf31-39869d972a6b

-- Sol generated from Geometry/ToricCode/Homology.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_card_edge
import Theorems.Thm_ToricCode_one_le_mul
import Theorems.Thm_ToricCode_rank_d1
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
theorem solution: Module.finrank F2 (cycles M N) = M * N + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (d1 M N).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, card_edge M N] at h
  have hr : Module.finrank F2 (LinearMap.range (d1 M N).mulVecLin) = M * N - 1 := rank_d1 M N
  have := one_le_mul M N
  show Module.finrank F2 (LinearMap.ker (d1 M N).mulVecLin) = M * N + 1
  omega
