-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_retraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:41.661176+00:00
-- url     : https://prove2.me/submissions/54bb64e8-185c-4047-8f9c-a0357911667f

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice

set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
namespace Kourovka.CentralLattice
theorem _root_.solution [Module.Finite ℤ M] (D : Submodule ℤ M) :
    ∃ p : M →ₗ[ℤ] saturation D, ∀ x : saturation D, p x = x := by
  let S := saturation D
  letI : NoZeroSMulDivisors ℤ (M ⧸ S) := quotientSaturation_torsionFree D
  letI : Module.IsTorsionFree ℤ (M ⧸ S) := (Module.isTorsionFree_iff_smul_eq_zero).mpr (fun r m h => (quotientSaturation_torsionFree D).eq_zero_or_eq_zero_of_smul_eq_zero h)
  letI : Module.Finite ℤ (M ⧸ S) := Module.Finite.of_surjective S.mkQ S.mkQ_surjective
  obtain ⟨j, hj⟩ := Module.projective_lifting_property S.mkQ
    (LinearMap.id : M ⧸ S →ₗ[ℤ] M ⧸ S) S.mkQ_surjective
  let p : M →ₗ[ℤ] S := (LinearMap.id - j.comp S.mkQ).codRestrict S (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero S).mp
    change S.mkQ (x - j (S.mkQ x)) = 0
    rw [map_sub]
    have he := congrArg (fun f : M ⧸ S →ₗ[ℤ] M ⧸ S => f (S.mkQ x)) hj
    change S.mkQ (j (S.mkQ x)) = S.mkQ x at he
    rw [he, sub_self]
    rfl)
  refine ⟨p, ?_⟩
  intro x
  apply Subtype.ext
  change x.val - j (S.mkQ x.val) = x.val
  have hx : S.mkQ x.val = 0 := (Submodule.Quotient.mk_eq_zero S).mpr x.property
  simp [hx]
end Kourovka.CentralLattice
