-- Prove2me | Theorems.Thm_Kourovka_CentralPeriod_quotientMap_iterate
-- name    : Kourovka.CentralPeriod.quotientMap_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:07.902181+00:00
-- url     : https://prove2.me/theorems/98cb2afd-db8b-45c3-b023-b56a423db311
-- title:
--   Central Period: quotient Map iterate
-- statement:
--   The Central Period construction uses the quotient Map iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L41-L47
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralPeriod.lean#L41-L47

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]

theorem Kourovka.CentralPeriod.quotientMap_iterate (f : M →ₗ[ℤ] M) (d : ℤ) (n : ℕ) (x : M) :
    (quotientMap M f d)^[n] ((multiples M d).mkQ x) = (multiples M d).mkQ (f^[n] x) := by sorry
