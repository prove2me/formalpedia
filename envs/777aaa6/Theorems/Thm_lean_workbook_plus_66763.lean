-- Prove2me | Theorems.Thm_lean_workbook_plus_66763
-- name    : lean_workbook_plus_66763
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/dea802f0-e7f3-4bd8-b2a2-e2898df16f66
-- statement:
--   Show that: $\frac{1}{2}\cdot\frac{3}{4}\cdot\frac{5}{6}\cdots\frac{99}{100} < \frac{1}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66763 : (∏ i in Finset.range 100, (2 * i + 1) / (2 * i + 2)) < 1 / 10   :=  by sorry
