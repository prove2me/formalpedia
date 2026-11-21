-- Prove2me | solution 1 for Kourovka.CentralPeriod.multiples_quotient_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:35.596279+00:00
-- url     : https://prove2.me/submissions/503d47a9-a2fe-4a9d-8cf6-43ca742721dd

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod

set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]
namespace Kourovka.CentralPeriod
theorem _root_.solution [Module.Finite ℤ M] (d : ℤ) (hd : d ≠ 0) :
    Finite (M ⧸ multiples M d) := by
  letI : Module.Finite ℤ (M ⧸ multiples M d) := Module.Finite.of_surjective (multiples M d).mkQ (multiples M d).mkQ_surjective
  apply Module.finite_of_fg_torsion
  intro x
  obtain ⟨x, rfl⟩ := (multiples M d).mkQ_surjective x
  refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
  change d • (multiples M d).mkQ x = 0
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨x, rfl⟩
end Kourovka.CentralPeriod
