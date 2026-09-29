-- Prove2me | Theorems.Thm_ToricCode_hammingNorm_comp_equiv
-- name    : ToricCode.hammingNorm_comp_equiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:12:29.359351+00:00
-- url     : https://prove2.me/theorems/a32ac83e-9193-4b46-b44f-3bbd4b00f58c
-- title:
--   HammingNorm comp equiv
-- statement:
--   Formal statement of `ToricCode.hammingNorm_comp_equiv` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ToricCode.hammingNorm_comp_equiv{α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
--       (e : α ≃ β) (z : β → F2) : hammingNorm (z ∘ e) = hammingNorm z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Dual.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Dual.lean#L155

-- Thm stub generated from Geometry/ToricCode/Dual.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Dual
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

theorem ToricCode.hammingNorm_comp_equiv{α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (z : β → F2) : hammingNorm (z ∘ e) = hammingNorm z := by sorry
