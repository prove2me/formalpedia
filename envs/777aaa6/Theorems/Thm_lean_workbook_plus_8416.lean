-- Prove2me | Theorems.Thm_lean_workbook_plus_8416
-- name    : lean_workbook_plus_8416
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7e1649aa-d2e1-4b5e-94d6-2b3d8f7ed19f
-- statement:
--   Prove that $2(ab+bc+ca)-a^2-b^2-c^2 > 0$ for a triangle with sides $a$, $b$, and $c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8416 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a * b + b * c + c * a) - a ^ 2 - b ^ 2 - c ^ 2 > 0   :=  by sorry
