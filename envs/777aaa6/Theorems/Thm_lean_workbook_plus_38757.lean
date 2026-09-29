-- Prove2me | Theorems.Thm_lean_workbook_plus_38757
-- name    : lean_workbook_plus_38757
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/1c1c815f-5641-4852-a4f9-7118cf6a8fe0
-- statement:
--   Show that $2^y-1$ divides $2^n-1$ where $y$ is a divisor of $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38757 {y n : ℕ} (h : y ∣ n) : 2 ^ y - 1 ∣ 2 ^ n - 1   :=  by sorry
