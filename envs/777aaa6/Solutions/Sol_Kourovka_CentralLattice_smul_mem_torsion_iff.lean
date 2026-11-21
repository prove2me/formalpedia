-- Prove2me | solution 1 for Kourovka.CentralLattice.smul_mem_torsion_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:00.549173+00:00
-- url     : https://prove2.me/submissions/26894a4e-f8cf-49f1-b263-99b427df7134

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
theorem _root_.solution {d : ℤ} (hd : d ≠ 0) (x : M) :
    d • x ∈ Submodule.torsion ℤ M ↔ x ∈ Submodule.torsion ℤ M := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n * ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    exact (mul_smul (n : ℤ) d x).trans hn
  · exact (Submodule.torsion ℤ M).smul_mem d
end Kourovka.CentralLattice
