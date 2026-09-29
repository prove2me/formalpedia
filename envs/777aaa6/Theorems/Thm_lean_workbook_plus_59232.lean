-- Prove2me | Theorems.Thm_lean_workbook_plus_59232
-- name    : lean_workbook_plus_59232
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2f5a0d7e-d727-4473-b91b-f9a82a84c5b1
-- statement:
--   Show that $9^{n} - 1$ is divisible by $9$ for all $n >= 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59232 (n:ℕ) (hn: 1 ≤ n) : 9 ∣ 9^n - 1   :=  by sorry
