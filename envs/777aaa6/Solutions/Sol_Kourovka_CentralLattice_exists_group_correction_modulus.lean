-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_group_correction_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:31.76464+00:00
-- url     : https://prove2.me/submissions/819bd265-c253-499c-953e-8117737ba9ae

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
import Theorems.Thm_Kourovka_CentralLattice_exists_uniform_correction_modulus
import Theorems.Thm_Kourovka_CentralLattice_abelianMap_centralCorrection
import Theorems.Thm_Kourovka_centralCorrection_surjective


set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
variable {G : Type*} [Group G]
namespace Kourovka.CentralLattice
theorem _root_.solution [Group.FG G] :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ u : G →* G,
      (∀ z ∈ Subgroup.center G, u z ∈ Subgroup.center G) →
      (∀ y, ∃ x z, z ∈ Subgroup.center G ∧ u x * z = y) →
      (∀ x : Additive (Abelianization G), ∃ y, abelianMap u x - x = d • y) →
      (∀ y ∈ commutator G, ∃ x ∈ commutator G, u x = y) →
      ∃ h : G →* Subgroup.center G, Function.Surjective (centralCorrection u h) := by
  letI : Group.FG (Abelianization G) :=
    Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective
  letI : Module.Finite ℤ (Additive (Abelianization G)) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨d, hd, hmod⟩ := exists_uniform_correction_modulus (centerImage (G := G))
  refine ⟨d, hd, ?_⟩
  intro u hcenter hrow hcong hder
  have hu : ∀ x ∈ LinearMap.range (centerImage (G := G)),
      abelianMap u x ∈ LinearMap.range (centerImage (G := G)) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨Additive.ofMul (⟨u z.toMul.val, hcenter z.toMul.val z.toMul.property⟩ :
      Subgroup.center G), ?_⟩
    rfl
  have hrowAb : ∀ y : Additive (Abelianization G),
      ∃ x z, abelianMap u x + centerImage z = y := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨x, z, hz, hxy⟩ := hrow y
    refine ⟨Additive.ofMul (Abelianization.of x), Additive.ofMul (⟨z, hz⟩ : Subgroup.center G), ?_⟩
    change Abelianization.of (u x) * Abelianization.of z = Abelianization.of y
    rw [← map_mul, hxy]
  obtain ⟨k, hk⟩ := hmod (abelianMap u) hu hrowAb hcong
  refine ⟨centralLift k, centralCorrection_surjective u (centralLift k) hder ?_⟩
  rw [← abelianMap_centralCorrection u k] at hk
  exact hk
end Kourovka.CentralLattice
