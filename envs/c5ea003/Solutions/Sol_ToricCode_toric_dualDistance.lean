-- Prove2me | solution 1 for ToricCode.toric_dualDistance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:54:39.196544+00:00
-- url     : https://prove2.me/submissions/4e39391b-da5a-4150-9bb3-aca326b6218a

-- Sol generated from Geometry/ToricCode/Dual.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Dual
import Theorems.Thm_ToricCode_dualLogicalWeights_eq
import Theorems.Thm_ToricCode_toric_distance
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
theorem solution: dualDistance M N = min M N := by
  rw [dualDistance, dualLogicalWeights_eq]
  exact toric_distance M N
