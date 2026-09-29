-- Prove2me | Theorems.Thm_lean_workbook_plus_46907
-- name    : lean_workbook_plus_46907
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/549b3447-ab76-4c45-b887-6cf236ca610d
-- statement:
--   Now we can see that the inquality $\sum a^3 \ge \sum b(a-c)^2+3abc$ is equivalent to schur inequality
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46907 {a b c : ℝ} (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) : a ^ 3 + b ^ 3 + c ^ 3 ≥ b * (a - c) ^ 2 + c * (b - a) ^ 2 + a * (c - b) ^ 2 + 3 * a * b * c   :=  by sorry
