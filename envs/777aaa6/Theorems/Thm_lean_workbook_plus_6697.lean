-- Prove2me | Theorems.Thm_lean_workbook_plus_6697
-- name    : lean_workbook_plus_6697
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/57ca55b2-b848-4fe3-ae73-2297463cb426
-- statement:
--   Show that: $\frac{1}{2}\times \frac{3}{4}\times \frac{5}{6}\times ....\times \frac{99}{100}< \frac{1}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6697 : (∏ i in Finset.range 50, (2 * i + 1) / (2 * i + 2)) < 1 / 10   :=  by sorry
