-- Prove2me | Theorems.Thm_lean_workbook_plus_1735
-- name    : lean_workbook_plus_1735
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e3b14e02-c08b-4cb5-b03e-7fc2eef04428
-- statement:
--   Let $a,b,c \in (0,1)$ so that $a^2+b^2+c^2=1$ . Prove that $12 \sqrt[4]{abc(1-a)(1-b)(1-c)} \leq 4 +(a+b+c-1)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1735 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) (hab : a + b + c = 1) : 12 * (abc * (1 - a) * (1 - b) * (1 - c)) ^ (1 / 4) ≤ 4 + (a + b + c - 1) ^ 2   :=  by sorry
