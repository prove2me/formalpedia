-- Prove2me | Theorems.Thm_lean_workbook_plus_15426
-- name    : lean_workbook_plus_15426
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/456a27af-7628-4dca-a1dc-e89a5a021a4d
-- statement:
--   Let $ a \ge b \ge c \0 $ and $ a+c \ge 2b$ , $ a \le 2c$ . Prove that : $ 2\left(\sum{a}\right)^3 + 27abc \ge 9(ab+bc+ca)(a+b+c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15426 (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c ≥ 0) (h2 : a + c ≥ 2 * b) (h3 : a ≤ 2 * c) : 2 * (a + b + c) ^ 3 + 27 * a * b * c ≥ 9 * (a * b + b * c + c * a) * (a + b + c)   :=  by sorry
