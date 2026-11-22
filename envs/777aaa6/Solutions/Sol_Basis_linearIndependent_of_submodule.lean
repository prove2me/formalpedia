-- Prove2me | solution 1 for Basis.linearIndependent_of_submodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:41:34.922774+00:00
-- url     : https://prove2.me/submissions/e22da8b6-beb4-4331-8f8a-da6e1cdd4cda

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
import Definitions.Def_BruhatTits_Utils_Subring

set_option autoImplicit false
universe uCompat vCompat wCompat
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
omit [DecidableEq ι]
variable {K : Type*} [Field K]
variable {R : Subring K} [IsFractionRing R K]
namespace Basis
theorem _root_.solution {κ : Type*} {M : Submodule R (ι → K)} (b : Basis κ R M) :
    LinearIndependent K (fun i ↦ (b i).val) := by
  rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
  intro s g hs
  simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
  exact linearIndependent_iff'.mp b.linearIndependent s g hs
end Basis
