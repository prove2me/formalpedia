-- Prove2me | Theorems.Thm_lean_workbook_plus_11894
-- name    : lean_workbook_plus_11894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/52b6a290-ebff-4505-b57c-cf831e4a1ed8
-- statement:
--   Prove that \n $$\frac{5}{n(n+5)}=\frac{1}{n}-\frac{1}{n+5}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11894 : ∀ n : ℝ, n ≠ 0 ∧ n + 5 ≠ 0 → 5 / (n * (n + 5)) = 1 / n - 1 / (n + 5)   :=  by sorry
