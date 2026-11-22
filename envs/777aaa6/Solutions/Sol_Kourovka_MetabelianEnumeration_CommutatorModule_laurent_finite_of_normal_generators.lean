-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.laurent_finite_of_normal_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:29.227182+00:00
-- url     : https://prove2.me/submissions/4fb0c002-5c65-46b3-ab9d-d338e6e8c88b

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Modules_LaurentAction
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_single_image

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (hq : Function.Surjective q)
    (s : Finset π.ker)
    (hs : Subgroup.normalClosure (Subtype.val '' (s : Set π.ker)) = π.ker) :
    letI := laurentModule π hπ q
    Module.Finite (AddMonoidAlgebra ℤ L) (Additive π.ker) := by
  classical
  letI := laurentModule π hπ q
  let fs : Finset (Additive π.ker) := s.image Additive.ofMul
  let V : Submodule (AddMonoidAlgebra ℤ L) (Additive π.ker) :=
    Submodule.span _ (fs : Set (Additive π.ker))
  let B : Subgroup E := V.toAddSubgroup.toSubgroup'.map π.ker.subtype
  have hconj (g : E) (a : π.ker) (ha : Additive.ofMul a ∈ V) :
      Additive.ofMul (MulAut.conjNormal g a) ∈ V := by
    obtain ⟨u, hu⟩ := hq (π g⁻¹)
    have hact : (((AddMonoidAlgebra.single u.toAdd 1 : AddMonoidAlgebra ℤ L) •
        Additive.ofMul a) : Additive π.ker) =
        Additive.ofMul (MulAut.conjNormal g a) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [laurent_single_image π hπ q u.toAdd g⁻¹ hu, inv_inv]
      rfl
    rw [← hact]
    exact V.smul_mem _ ha
  letI : B.Normal := {
    conj_mem := by
      rintro _ ⟨a, ha, rfl⟩ g
      exact ⟨MulAut.conjNormal g a, hconj g a ha, rfl⟩ }
  have hsub : Subtype.val '' (s : Set π.ker) ⊆ B := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    change Additive.ofMul a ∈ V
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hker : π.ker ≤ B := by
    rw [← hs]
    exact Subgroup.normalClosure_le_normal hsub
  have hspan : V = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b, hb, hba⟩ := hker a.toMul.property
    have hba' : b = a.toMul := Subtype.ext hba
    simpa only [hba'] using hb
  exact ⟨fs, hspan⟩
end Kourovka.MetabelianEnumeration.CommutatorModule
