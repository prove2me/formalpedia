-- Prove2me | Theorems.Thm_lean_workbook_plus_74404
-- name    : lean_workbook_plus_74404
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/869d98de-4e71-4cbe-bb3c-8acffbbcafa4
-- statement:
--   If $a \ge 0$ , then $5(a^2-a+1)^2 \ge 2(1+a^4)$ . Prove.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74404 (a : ℝ) (ha : a ≥ 0) : 5 * (a ^ 2 - a + 1) ^ 2 ≥ 2 * (1 + a ^ 4)   :=  by sorry
