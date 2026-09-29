-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_55698
-- name    : WorkbookCorrected.plus_55698
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:20:30.886987+00:00
-- url     : https://prove2.me/theorems/0b8eaff2-0ac1-410b-9e45-5638f77aeb00
-- title:
--   Binomial coefficient value #55698
-- statement:
--   $\binom{24-4}{5} = \binom{20}{5} = 15504$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_55698`, which used bare `choose` (unresolvable under its narrow preamble) and was missing the `:` type annotation.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_55698 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_55698 : Nat.choose (24 - 4) 5 = 15504 := by sorry
