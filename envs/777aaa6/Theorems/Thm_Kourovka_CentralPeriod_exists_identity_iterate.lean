-- Prove2me | Theorems.Thm_Kourovka_CentralPeriod_exists_identity_iterate
-- name    : Kourovka.CentralPeriod.exists_identity_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:08.640657+00:00
-- url     : https://prove2.me/theorems/fdbeb3b4-7b5a-44aa-9255-47622a74b31f
-- title:
--   Central Period: exists identity iterate
-- statement:
--   A surjection of a finite type has a positive iterate equal to the identity.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L50-L57
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L50-L57

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]

theorem Kourovka.CentralPeriod.exists_identity_iterate {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Surjective f) : ∃ n : ℕ, 0 < n ∧ f^[n] = id := by sorry
