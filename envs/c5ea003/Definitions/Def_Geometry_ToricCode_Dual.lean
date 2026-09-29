-- Prove2me | Definitions.Def_Geometry_ToricCode_Dual
-- name    : Geometry_ToricCode_Dual
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:54:25.963867+00:00
-- url     : https://prove2.me/theorems/c4834ecf-23dc-4718-9ec2-ac9e2e1bd01f
-- title:
--   Aether Catalog definitions — Geometry_ToricCode_Dual
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ToricCode.Dual`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ToricCode/Dual.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Theorems.Thm_ToricCode_d1T_mulVec
import Theorems.Thm_ToricCode_d2T_mulVec
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

namespace ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

/-! ### The quarter-turn duality of the square lattice -/

/-- The quarter-turn permutation of the edge set: it exchanges horizontal and
vertical edges, matching each edge with the dual edge it crosses. -/
def tau : Edge M N → Edge M N := fun e => (!e.1, e.2 - step M N (!e.1))

/-- The inverse quarter turn. -/
def tauInv : Edge M N → Edge M N := fun e => (!e.1, e.2 + step M N e.1)

omit [NeZero M] [NeZero N] in
lemma tau_tauInv (e : Edge M N) : tau M N (tauInv M N e) = e := by
  obtain ⟨b, u⟩ := e
  simp only [tau, tauInv, Bool.not_not]
  cases b <;> simp

omit [NeZero M] [NeZero N] in
lemma tauInv_tau (e : Edge M N) : tauInv M N (tau M N e) = e := by
  obtain ⟨b, u⟩ := e
  simp only [tau, tauInv, Bool.not_not]
  cases b <;> simp

/-- The quarter turn as a permutation of the qubit set. -/
def tauEquiv : Edge M N ≃ Edge M N where
  toFun := tau M N
  invFun := tauInv M N
  left_inv := tauInv_tau M N
  right_inv := tau_tauInv M N

/-- **Self-duality of the boundary maps.**  Precomposing with the quarter turn
turns the cellular boundary `d₁` into the dual boundary `d₂ᵀ`. -/
theorem d2T_mulVec_comp_tau (z : Edge M N → F2) :
    ((d2 M N)ᵀ *ᵥ (z ∘ tau M N)) = (d1 M N *ᵥ z) := by
  funext f
  rw [d2T_mulVec, d1_mulVec]
  simp only [Function.comp_apply, tau, Bool.not_false, Bool.not_true, step_false, step_true]
  have e1 : (f + ((0 : ZMod M), (1 : ZMod N))) - (0, 1) = f := by simp
  have e2 : (f + ((1 : ZMod M), (0 : ZMod N))) - (1, 0) = f := by simp
  rw [e1, e2]
  ring

/-- The quarter turn carries `2`-boundaries to `0`-coboundaries. -/
theorem d2_comp_tau (g : Face M N → F2) :
    ((d2 M N *ᵥ g) ∘ tau M N) = (d1 M N)ᵀ *ᵥ (fun u => g (u - (1, 1))) := by
  funext e
  obtain ⟨b, u⟩ := e
  rw [Function.comp_apply, d1T_mulVec]
  obtain ⟨p, q⟩ := u
  cases b
  · have ht : tau M N (false, (p, q)) = (true, (p, q) - (0, 1)) := by simp [tau]
    rw [ht, d2_mulVec]
    have a2 : ((p, q) : ZMod M × ZMod N) - (0, 1) - step M N (!true) = (p, q) - (1, 1) := by
      simp only [Bool.not_true, step_false, Prod.mk_sub_mk, Prod.mk.injEq]
      constructor <;> ring
    have a1 : ((p, q) : ZMod M × ZMod N) - (0, 1) = ((p, q) + step M N false) - (1, 1) := by
      simp only [step_false, Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> ring
    rw [a2, a1]
    ring
  · have ht : tau M N (true, (p, q)) = (false, (p, q) - (1, 0)) := by simp [tau]
    rw [ht, d2_mulVec]
    have a2 : ((p, q) : ZMod M × ZMod N) - (1, 0) - step M N (!false) = (p, q) - (1, 1) := by
      simp only [Bool.not_false, step_true, Prod.mk_sub_mk, Prod.mk.injEq]
      constructor <;> ring
    have a1 : ((p, q) : ZMod M × ZMod N) - (1, 0) = ((p, q) + step M N true) - (1, 1) := by
      simp only [step_true, Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> ring
    rw [a2, a1]
    ring


/-! ### The dual code -/

/-- Dual (`X`-type) cycles: cochains killed by the dual boundary `d₂ᵀ`. -/
noncomputable def dualCycles : Submodule F2 (Edge M N → F2) :=
  LinearMap.ker ((d2 M N)ᵀ).mulVecLin

/-- Dual (`X`-type) boundaries: the image of the coboundary `d₁ᵀ`. -/
noncomputable def dualBoundaries : Submodule F2 (Edge M N → F2) :=
  LinearMap.range ((d1 M N)ᵀ).mulVecLin


/-- Dual homology rank: the dual code also encodes two logical qubits. -/
noncomputable def dualHomologyRank : ℕ :=
  Module.finrank F2 (dualCycles M N) - Module.finrank F2 (dualBoundaries M N)


/-! ### The dual distance -/

/-- Weights of the logical `X` operators. -/
def dualLogicalWeights : Set ℕ :=
  {w | ∃ z : Edge M N → F2, z ∈ dualCycles M N ∧ z ∉ dualBoundaries M N ∧ hammingNorm z = w}

/-- The `X`-distance of the toric code. -/
noncomputable def dualDistance : ℕ := sInf (dualLogicalWeights M N)






end ToricCode


