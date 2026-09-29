-- Prove2me | solution 1 for ToricCode.toric_dual_homologyRank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:54:39.887676+00:00
-- url     : https://prove2.me/submissions/d8b0cda9-19c7-41c0-b0eb-6209914a9cb3

-- Sol generated from Geometry/ToricCode/Dual.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Dual
import Theorems.Thm_ToricCode_card_edge
import Theorems.Thm_ToricCode_one_le_mul
import Theorems.Thm_ToricCode_rank_d1
import Theorems.Thm_ToricCode_rank_d2
/-!
# The dual (`X`-type) toric code, and the total code distance

A CSS code has two distances: the `Z`-distance measured on `ker d₁ / im d₂`
(computed in `ToricCode.Distance`) and the `X`-distance measured on the
*cochain* complex `ker d₂ᵀ / im d₁ᵀ`.

The square torus is **self-dual**: rotating the lattice by a quarter turn
exchanges vertices with faces and horizontal with vertical edges.  We make this
explicit as an involutive-style permutation `tauEquiv` of the edge set and prove

* `d2T_mulVec_comp_tau` : `d₂ᵀ (z ∘ τ) = d₁ z`,
* `d2_comp_tau` and `d1T_eq` : `τ` matches boundaries with coboundaries,

so that `τ` carries the primal logical operators bijectively onto the dual ones,
preserving Hamming weight.  Consequently

* `dualLogicalWeights_eq` : the two logical weight spectra are *equal*,
* `toric_dualDistance` : the `X`-distance is also `min M N`,
* `toric_totalDistance` : the total code distance `min d_X d_Z` equals `min M N`,
* `toric_full_parameters` : the toric code is an `[[2MN, 2, min M N]]` CSS code with
  matching primal and dual systoles.

Finally `toric_dual_homologyRank` shows the dual code also encodes two logical
qubits, as it must.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

/-! ### The quarter-turn duality of the square lattice -/









/-! ### The dual code -/






/-! ### The dual distance -/









open ToricCode in
theorem solution: dualHomologyRank M N = 2 := by
  have hk := LinearMap.finrank_range_add_finrank_ker ((d2 M N)ᵀ).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, card_edge] at hk
  have hr2 : Module.finrank F2 (LinearMap.range ((d2 M N)ᵀ).mulVecLin) = M * N - 1 := by
    show ((d2 M N)ᵀ).rank = M * N - 1
    rw [Matrix.rank_transpose]
    exact rank_d2 M N
  have hr1 : Module.finrank F2 (dualBoundaries M N) = M * N - 1 := by
    show ((d1 M N)ᵀ).rank = M * N - 1
    rw [Matrix.rank_transpose]
    exact rank_d1 M N
  have := one_le_mul M N
  rw [dualHomologyRank, hr1]
  show Module.finrank F2 (LinearMap.ker ((d2 M N)ᵀ).mulVecLin) - (M * N - 1) = 2
  omega
