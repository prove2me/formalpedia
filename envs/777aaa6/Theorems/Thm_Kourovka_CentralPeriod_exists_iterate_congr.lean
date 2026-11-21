-- Prove2me | Theorems.Thm_Kourovka_CentralPeriod_exists_iterate_congr
-- name    : Kourovka.CentralPeriod.exists_iterate_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:20.276019+00:00
-- url     : https://prove2.me/theorems/92df048d-97d7-47cd-86d6-c85004079d60
-- title:
--   Central Period: exists iterate congr
-- statement:
--   A positive power of a surjective endomorphism is the identity modulo every nonzero modulus.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L60-L74
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L60-L74

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]

theorem Kourovka.CentralPeriod.exists_iterate_congr [Module.Finite ℤ M] (f : M →ₗ[ℤ] M)
    (hf : Function.Surjective f) (d : ℤ) (hd : d ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : M, ∃ y : M, f^[n] x - x = d • y := by sorry
