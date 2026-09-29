-- Prove2me | Theorems.Thm_lean_workbook_plus_17527
-- name    : lean_workbook_plus_17527
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d81a6abe-1a85-44e6-a43b-2d76e1cae7e6
-- statement:
--   For $n\ge 3$, $17^{n-1}\cdot 2^{n^2}-1 > 9n^2\cdot 2^{n^2}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17527 (n : ℕ) (hn : 3 ≤ n) : (17:ℝ)^(n-1) * 2^(n^2) - 1 > 9 * n^2 * 2^(n^2) - 1   :=  by sorry
