-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.lattice_kernel_finite_module
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:42.974421+00:00
-- url     : https://prove2.me/submissions/2dea4307-2a6b-4ea6-b74a-3ecbe4ccf7b8

import Definitions.Def_Kourovka_Presentations_KernelGenerators
import Definitions.Def_Kourovka_Modules_LaurentAction
import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_lattice_kernel_finite_normal_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_finite_of_normal_generators


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    letI := lattice_kernel_commutative R hG
    letI := laurentModule (latticeProjection R) (latticeProjection_surjective R)
      (MonoidHom.id (Multiplicative (Lattice k)))
    Module.Finite (AddMonoidAlgebra ℤ (Lattice k)) (Additive (latticeProjection R).ker) := by
  letI := lattice_kernel_commutative R hG
  obtain ⟨s, hs⟩ := lattice_kernel_finite_normal_generators R
  exact laurent_finite_of_normal_generators (latticeProjection R)
    (latticeProjection_surjective R) (MonoidHom.id (Multiplicative (Lattice k)))
    Function.surjective_id s hs
end Kourovka.MetabelianEnumeration.CofinalCover
