-- Prove2me | Theorems.Thm_lean_workbook_plus_71651
-- name    : lean_workbook_plus_71651
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4a574164-a2a0-422f-9072-8580ac163cc6
-- statement:
--   Now using the first piece to get an equation with $o$ in terms of $g$ $0.2g + 0.5o = 24$ so $0.5o = 24 - 0.2g$ and $o = 48 - 0.4g.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71651 (g o : ℝ) : 0.2 * g + 0.5 * o = 24 → o = 48 - 0.4 * g   :=  by sorry
