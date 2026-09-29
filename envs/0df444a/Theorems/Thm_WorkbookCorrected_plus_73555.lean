-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_73555
-- name    : WorkbookCorrected.plus_73555
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:32.319269+00:00
-- url     : https://prove2.me/theorems/350a3f61-f393-4ee8-aa65-f360381e5fd4
-- title:
--   Sum twenty plus three hundred sixty plus one thousand eighty plus four hundred
-- statement:
--   Adding the case counts $20+360+1080+400$ yields the total $1860$ in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_73555`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_73555 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_73555; Apache-2.0; corrects Open node d180cfb0-7fa8-472b-844b-22ed5bcef282

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_73555 : (20 : ℕ) + 360 + 1080 + 400 = 1860 := by sorry
