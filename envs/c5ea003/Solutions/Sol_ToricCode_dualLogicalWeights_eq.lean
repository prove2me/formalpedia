-- Prove2me | solution 1 for ToricCode.dualLogicalWeights_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:46:47.560984+00:00
-- url     : https://prove2.me/submissions/29df99a8-103a-416f-9a45-9dce93c48585

-- Sol generated from Geometry/ToricCode/Dual.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Dual
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_hammingNorm_comp_equiv
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








/-- Conversely, every `0`-coboundary is the quarter turn of a `2`-boundary. -/
theorem d1T_eq_comp_tau (h : Vert M N → F2) :
    (d1 M N)ᵀ *ᵥ h = ((d2 M N *ᵥ (fun u => h (u + (1, 1)))) ∘ tau M N) := by
  rw [d2_comp_tau]
  congr 1
  funext u
  rw [sub_add_cancel]

/-! ### The dual code -/






/-! ### The dual distance -/









open ToricCode in
theorem solution: dualLogicalWeights M N = logicalWeights M N := by
  ext w
  constructor
  · rintro ⟨z, hz, hnb, rfl⟩
    refine ⟨z ∘ tauInv M N, ?_, ?_, ?_⟩
    · rw [cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have := d2T_mulVec_comp_tau M N (z ∘ tauInv M N)
      have hzz : (z ∘ tauInv M N) ∘ tau M N = z := by
        funext e; simp [Function.comp_apply, tauInv_tau]
      rw [hzz] at this
      rw [← this]
      rw [dualCycles, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
      exact hz
    · intro hb
      apply hnb
      obtain ⟨g, hg⟩ := hb
      refine ⟨fun u => g (u - (1, 1)), ?_⟩
      rw [Matrix.mulVecLin_apply, ← d2_comp_tau]
      rw [Matrix.mulVecLin_apply] at hg
      rw [hg]
      funext e
      simp [Function.comp_apply, tauInv_tau]
    · exact hammingNorm_comp_equiv (tauEquiv M N).symm z
  · rintro ⟨z, hz, hnb, rfl⟩
    refine ⟨z ∘ tau M N, ?_, ?_, ?_⟩
    · rw [dualCycles, LinearMap.mem_ker, Matrix.mulVecLin_apply, d2T_mulVec_comp_tau]
      rw [cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
      exact hz
    · intro hb
      apply hnb
      obtain ⟨h, hh⟩ := hb
      refine ⟨fun u => h (u + (1, 1)), ?_⟩
      rw [Matrix.mulVecLin_apply] at hh ⊢
      have hkey := d1T_eq_comp_tau M N h
      rw [hh] at hkey
      funext e
      have := congrFun hkey (tauInv M N e)
      simpa [Function.comp_apply, tau_tauInv] using this.symm
    · exact hammingNorm_comp_equiv (tauEquiv M N) z
