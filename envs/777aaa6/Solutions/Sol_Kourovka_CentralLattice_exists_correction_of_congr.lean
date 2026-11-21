-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_correction_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:33.534119+00:00
-- url     : https://prove2.me/submissions/c7edd45f-3af3-463a-bab4-8fa53b71f937

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
import Theorems.Thm_Kourovka_CentralLattice_exists_free_correction
import Theorems.Thm_Kourovka_CentralLattice_eq_on_torsion_of_congr

set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
namespace Kourovka.CentralLattice
theorem _root_.solution [Module.Finite ℤ M]
    (c : Z →ₗ[ℤ] M) (u : M →ₗ[ℤ] M) (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ x ∈ saturation (LinearMap.range ((Submodule.torsion ℤ M).mkQ.comp c)),
      d • x ∈ LinearMap.range ((Submodule.torsion ℤ M).mkQ.comp c))
    (hkill : ∀ x ∈ Submodule.torsion ℤ M, d • x = 0)
    (hu : ∀ x ∈ LinearMap.range c, u x ∈ LinearMap.range c)
    (hrow : ∀ y, ∃ x z, u x + c z = y)
    (hcong : ∀ x, ∃ y, u x - x = d • y) :
    ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by
  let T := Submodule.torsion ℤ M
  letI : Module.Finite ℤ (M ⧸ T) := Module.Finite.of_surjective T.mkQ T.mkQ_surjective
  letI : Module.IsTorsionFree ℤ (M ⧸ T) := Submodule.QuotientTorsion.instIsTorsionFree
  letI quotientNoZero : NoZeroSMulDivisors ℤ (FreeQuotient M) := ⟨fun h => smul_eq_zero.mp h⟩
  let q : M →ₗ[ℤ] FreeQuotient M := (Submodule.torsion ℤ M).mkQ
  let cq : Z →ₗ[ℤ] FreeQuotient M := q.comp c
  have huq : ∀ x ∈ LinearMap.range cq, freeMap u x ∈ LinearMap.range cq := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hu (c z) ⟨z, rfl⟩
    exact ⟨w, congrArg q hw⟩
  have hrowq : ∀ y : FreeQuotient M, ∃ x z, freeMap u x + cq z = y := by
    intro y
    obtain ⟨y, rfl⟩ := T.mkQ_surjective y
    obtain ⟨x, z, hz⟩ := hrow y
    exact ⟨q x, z, by simpa only [map_add] using congrArg q hz⟩
  have hcongq : ∀ x : FreeQuotient M, ∃ y, freeMap u x - x = d • y := by
    intro x
    obtain ⟨x, rfl⟩ := T.mkQ_surjective x
    obtain ⟨y, hy⟩ := hcong x
    exact ⟨q y, by simpa only [map_sub, map_smul] using congrArg q hy⟩
  obtain ⟨k, hk⟩ := @exists_free_correction (FreeQuotient M) Z _ _ _ quotientNoZero cq (freeMap u) d hd hden huq hrowq hcongq
  let h := k.comp q
  let v := u + c.comp h
  have hqv : ∀ x, q (v x) = (freeMap u + cq.comp k) (q x) := by
    intro x
    change q (u x + c (k (q x))) = q (u x) + q (c (k (q x)))
    exact map_add q _ _
  have hvt : ∀ x ∈ T, v x = x := by
    intro x hx
    have hux := eq_on_torsion_of_congr u d hd hkill hcong x hx
    have hqx : q x = 0 := (Submodule.Quotient.mk_eq_zero T).mpr hx
    change u x + c (k (q x)) = x
    simp [hux, hqx]
  refine ⟨h, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := hk (q y)
  obtain ⟨x, rfl⟩ := T.mkQ_surjective a
  have hx : q (v x) = q y := (hqv x).trans ha
  have ht : y - v x ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change q (y - v x) = 0
    rw [map_sub, hx, sub_self]
    rfl
  refine ⟨x + (y - v x), ?_⟩
  change v (x + (y - v x)) = y
  rw [map_add, hvt _ ht]
  simp [sub_eq_add_neg, add_left_comm]
end Kourovka.CentralLattice
