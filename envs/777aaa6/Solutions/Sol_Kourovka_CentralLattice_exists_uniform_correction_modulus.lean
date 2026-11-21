-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_uniform_correction_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:33.497195+00:00
-- url     : https://prove2.me/submissions/55e1f3a4-46e3-404d-b0ce-76bfb88e0d0f

import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Definitions.Def_Kourovka_CentralLattice
import Theorems.Thm_Kourovka_CentralLattice_exists_denominator
import Theorems.Thm_Kourovka_CentralLattice_exists_torsion_annihilator
import Theorems.Thm_Kourovka_CentralLattice_exists_correction_of_congr

set_option autoImplicit true
noncomputable section
open scoped nonZeroDivisors
open Kourovka Kourovka.CentralLattice
variable {M Z : Type*} [AddCommGroup M] [AddCommGroup Z]
namespace Kourovka.CentralLattice
theorem _root_.solution [Module.Finite ℤ M] (c : Z →ₗ[ℤ] M) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ u : M →ₗ[ℤ] M,
      (∀ x ∈ LinearMap.range c, u x ∈ LinearMap.range c) →
      (∀ y, ∃ x z, u x + c z = y) →
      (∀ x, ∃ y, u x - x = d • y) →
      ∃ h : M →ₗ[ℤ] Z, Function.Surjective (u + c.comp h) := by
  letI : Module.Finite ℤ (M ⧸ Submodule.torsion ℤ M) := Module.Finite.of_surjective (Submodule.torsion ℤ M).mkQ (Submodule.torsion ℤ M).mkQ_surjective
  let cq := (Submodule.torsion ℤ M).mkQ.comp c
  obtain ⟨d, hd, hden⟩ := exists_denominator (LinearMap.range cq)
  obtain ⟨e, he, hkill⟩ := exists_torsion_annihilator (M := M)
  refine ⟨d * e, mul_ne_zero hd he, ?_⟩
  intro u hu hrow hcong
  apply exists_correction_of_congr c u (d * e) (mul_ne_zero hd he) _ _ hu hrow hcong
  · intro x hx
    rw [mul_comm d e, mul_smul]
    exact (LinearMap.range cq).smul_mem e (hden x hx)
  · intro x hx
    rw [mul_smul, hkill x hx, smul_zero]
end Kourovka.CentralLattice
