-- Prove2me | Theorems.Thm_lean_workbook_plus_31850
-- name    : lean_workbook_plus_31850
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/2922b58b-6881-40a7-9e02-0496396104cb
-- statement:
--   Prove that for a triangle with side lengths $a, b, c$, $3(ab+bc+ca)\leq (a+b+c)^2<4(ab+bc+ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31850 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 < 4 * (a * b + b * c + c * a)   :=  by sorry
