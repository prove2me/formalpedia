-- Prove2me | solution 1 for Kourovka.CentralPeriod.exists_identity_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:53.850404+00:00
-- url     : https://prove2.me/submissions/5a0fcd42-c010-4ee5-8610-f4be2cb6a9bc

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
import Theorems.Thm_Kourovka_FinitePaths_exists_idempotent_iterate


set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]
namespace Kourovka.CentralPeriod
theorem _root_.solution {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Surjective f) : ∃ n : ℕ, 0 < n ∧ f^[n] = id := by
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hf
  obtain ⟨n, hn, he⟩ := FinitePaths.exists_idempotent_iterate f
  refine ⟨n, hn, funext fun x => ?_⟩
  apply hi.iterate n
  have h := congrFun he x
  simpa only [two_mul, Function.iterate_add_apply, id_eq] using h
end Kourovka.CentralPeriod
