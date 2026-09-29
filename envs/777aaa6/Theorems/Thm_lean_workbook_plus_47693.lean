-- Prove2me | Theorems.Thm_lean_workbook_plus_47693
-- name    : lean_workbook_plus_47693
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/2e14d581-5b5d-4c97-b472-4cf49804b7ab
-- statement:
--   Prove that $\frac{3a^2-1}{(3-2a^2)(a^2+2)}\geq\frac{27a^2-9}{49}$ for $a^2 \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47693 (a : ℝ) (ha : a^2 ≤ 1) : (3 * a^2 - 1) / ((3 - 2 * a^2) * (a^2 + 2)) ≥ (27 * a^2 - 9) / 49   :=  by sorry
