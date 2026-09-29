-- Prove2me | Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
-- name    : mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T18:14:40.287492+00:00
-- url     : https://prove2.me/theorems/de0b9c05-287e-428b-b650-19f84461ea8c
-- title:
--   The asymmetric-route scalar recurrence ledger replays and clears its comparator
-- statement:
--   The 181-row append-only scalar ledger of the Duan-Wu-Zhou fourth-power recursion passes its
--   own arithmetic check, and the natural-logarithm rate floor 155673/20000 is at most the rate
--   floor stored for the final (global) row.
--
--   Each row records a list of weighted child indices, a retained floor and a claimed rate floor;
--   the check verifies, row by row and in order, that every child weight is non-negative, that
--   every child index has already been assigned a rate, and that the row's claimed rate floor is
--   at most the weighted sum of the children's rates plus the row's retained floor. The rate
--   floors of the six (1,3,4)-type fourth-level rows are the conservative values attainable by the
--   asymmetric recursive construction; every retained floor is unchanged from the exact
--   entropy certificate.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data

open MME.DWZFourthScalarLedger
set_option autoImplicit false

theorem mme_dwz_fourth_exact_scalar_recurrence_ledger_ma :
    (checkLedger = true /\ naturalRateFloor <= finalRateFloor) ∧
    ((naturalRateFloor : Real) <= (finalRateFloor : Real)) := by sorry
