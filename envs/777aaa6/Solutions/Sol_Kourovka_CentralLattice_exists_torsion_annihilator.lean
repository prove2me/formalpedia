-- Prove2me | solution 1 for Kourovka.CentralLattice.exists_torsion_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:59.872173+00:00
-- url     : https://prove2.me/submissions/4399d747-7198-418c-8e45-0b6fd5957494

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
theorem _root_.solution [Module.Finite ℤ M] :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ Submodule.torsion ℤ M, d • x = 0 := by
  let T := Submodule.torsion ℤ M
  obtain ⟨d, hd, hd0⟩ := (Submodule.annihilator_top_inter_nonZeroDivisors
      (Submodule.torsion_isTorsion (R := ℤ) (M := M)))
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd0, ?_⟩
  intro x hx
  exact congrArg Subtype.val ((Submodule.mem_annihilator.mp hd) (⟨x, hx⟩ : T) Submodule.mem_top)
end Kourovka.CentralLattice
