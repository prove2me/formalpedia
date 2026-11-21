-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_denominator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:41.169806+00:00
-- url     : https://prove2.me/submissions/56e86f40-8c97-4143-9ef0-d505d64d0a20

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
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ saturation D, d • x ∈ D := by
  let S := saturation D
  let E : Submodule ℤ S := D.comap S.subtype
  letI : Module.Finite ℤ S := Module.Finite.of_injective S.subtype S.subtype_injective
  letI : Module.Finite ℤ (S ⧸ E) := Module.Finite.of_surjective E.mkQ E.mkQ_surjective
  have ht : Module.IsTorsion ℤ (S ⧸ E) := by
    intro x
    obtain ⟨x, rfl⟩ := E.mkQ_surjective x
    obtain ⟨n, hn, hx⟩ := (mem_saturation D x.val).mp x.property
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero E).mpr hx
  obtain ⟨d, hd, hd0⟩ := (Submodule.annihilator_top_inter_nonZeroDivisors ht)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd0, ?_⟩
  intro x hx
  have hzero := (Submodule.mem_annihilator.mp hd) (E.mkQ ⟨x, hx⟩) Submodule.mem_top
  exact (Submodule.Quotient.mk_eq_zero E).mp hzero
end Kourovka.CentralLattice
