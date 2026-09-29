-- Prove2me | Theorems.Thm_lean_workbook_plus_46118
-- name    : lean_workbook_plus_46118
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/388168e9-02ec-4a43-84dc-a6de1e646e2a
-- statement:
--   Prove: $3b < 2a + 6c$ given $a >0$ and $b^{2} < 4ac$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46118 (a b c : ℝ) (ha : 0 < a) (hb : b^2 < 4 * a * c) : 3 * b < 2 * a + 6 * c   :=  by sorry
