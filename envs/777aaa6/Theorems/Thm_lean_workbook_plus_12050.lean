-- Prove2me | Theorems.Thm_lean_workbook_plus_12050
-- name    : lean_workbook_plus_12050
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/fec145d5-338e-4e0f-ba00-0fdcf178decb
-- statement:
--   We can have Anita be $y$ and Basilio be $x$. The equations are $y=4.5+x$ and $6x+3y=36$. Solving these equations is $x=2.5$ and $y=7$. Therefore, Anita is 7 years old and Basilio is 4.5 years old.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12050 (x y : ℝ) (h₁ : y = 4.5 + x) (h₂ : 6 * x + 3 * y = 36) : y = 7 ∧ x = 2.5   :=  by sorry
