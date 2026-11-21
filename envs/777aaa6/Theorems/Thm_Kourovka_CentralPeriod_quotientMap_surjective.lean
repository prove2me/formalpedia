-- Prove2me | Theorems.Thm_Kourovka_CentralPeriod_quotientMap_surjective
-- name    : Kourovka.CentralPeriod.quotientMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:00.358582+00:00
-- url     : https://prove2.me/theorems/0eca4ba5-518b-4bae-93b2-e3643b51c5c3
-- title:
--   Central Period: quotient Map surjective
-- statement:
--   The Central Period construction uses the quotient Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L34-L39
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L34-L39

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]

theorem Kourovka.CentralPeriod.quotientMap_surjective (f : M →ₗ[ℤ] M) (hf : Function.Surjective f) (d : ℤ) :
    Function.Surjective (quotientMap M f d) := by sorry
