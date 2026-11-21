-- Prove2me | solution 1 for Kourovka.CentralPeriod.quotientMap_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:50.667562+00:00
-- url     : https://prove2.me/submissions/bb57921d-35b2-4813-af35-5582f8b39b95

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod

set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]
namespace Kourovka.CentralPeriod
theorem _root_.solution (f : M →ₗ[ℤ] M) (d : ℤ) (n : ℕ) (x : M) :
    (quotientMap M f d)^[n] ((multiples M d).mkQ x) = (multiples M d).mkQ (f^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl
end Kourovka.CentralPeriod
