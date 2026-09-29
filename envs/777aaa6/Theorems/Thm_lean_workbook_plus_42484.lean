-- Prove2me | Theorems.Thm_lean_workbook_plus_42484
-- name    : lean_workbook_plus_42484
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cf7079b5-6050-42b5-86ca-c9aaf1c51bcd
-- statement:
--   Let $ a,b,c > 0$ be such that $ a + b + c = 1$ . Prove that $ 1 - (a^2 + b^2 + c^2) \le \frac 3{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42484 (a b c : ℝ) (h : a + b + c = 1) : 1 - (a ^ 2 + b ^ 2 + c ^ 2) ≤ 3 / 4   :=  by sorry
