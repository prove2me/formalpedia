-- Prove2me | solution 1 for Kourovka.CentralPeriod.quotientMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:43.143621+00:00
-- url     : https://prove2.me/submissions/7d4202cc-08f0-481c-af2e-4846e8a40e63

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod

set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]
namespace Kourovka.CentralPeriod
theorem _root_.solution (f : M →ₗ[ℤ] M) (hf : Function.Surjective f) (d : ℤ) :
    Function.Surjective (quotientMap M f d) := by
  intro y
  obtain ⟨y, rfl⟩ := (multiples M d).mkQ_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(multiples M d).mkQ x, rfl⟩
end Kourovka.CentralPeriod
