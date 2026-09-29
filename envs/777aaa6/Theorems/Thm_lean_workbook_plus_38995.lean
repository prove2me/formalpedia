-- Prove2me | Theorems.Thm_lean_workbook_plus_38995
-- name    : lean_workbook_plus_38995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/92f5c769-7448-465a-a935-ce797dc20095
-- statement:
--   Let $x, y$ be integer numbers such that $3x + 7y$ is divisible by $19$ . Prove that $43x + 75y$ is also divisible by $19$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38995 (x y : ℤ) (h : 19 ∣ 3 * x + 7 * y) : 19 ∣ 43 * x + 75 * y   :=  by sorry
