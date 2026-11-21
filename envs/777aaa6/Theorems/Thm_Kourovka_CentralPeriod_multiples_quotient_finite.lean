-- Prove2me | Theorems.Thm_Kourovka_CentralPeriod_multiples_quotient_finite
-- name    : Kourovka.CentralPeriod.multiples_quotient_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:55.295503+00:00
-- url     : https://prove2.me/theorems/1f5f3f2c-eb3e-4289-908c-cc96139db7a1
-- title:
--   Central Period: multiples quotient finite
-- statement:
--   The Central Period construction uses the multiples quotient finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L16-L26
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L16-L26

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]

theorem Kourovka.CentralPeriod.multiples_quotient_finite [Module.Finite ℤ M] (d : ℤ) (hd : d ≠ 0) :
    Finite (M ⧸ multiples M d) := by sorry
