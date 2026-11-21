-- Prove2me | solution 1 for Kourovka.CentralLattice.le_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:37.87901+00:00
-- url     : https://prove2.me/submissions/17089222-d0e8-4326-ac76-4dc486543e6b

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
theorem _root_.solution (D : Submodule ℤ M) : D ≤ saturation D := by
  intro x hx
  exact (mem_saturation D x).mpr ⟨1, one_ne_zero, by simpa using hx⟩
end Kourovka.CentralLattice
