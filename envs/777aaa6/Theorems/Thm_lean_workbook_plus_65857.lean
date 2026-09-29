-- Prove2me | Theorems.Thm_lean_workbook_plus_65857
-- name    : lean_workbook_plus_65857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/2a068f5e-96d6-43cd-9e09-0439e65ad3f8
-- statement:
--   Prove that $\frac{n}{9n+7} < \frac{1}{9}$ for all $n \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65857 (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) / (9 * n + 7) < 1 / 9   :=  by sorry
