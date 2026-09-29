-- Prove2me | Theorems.Thm_lean_workbook_plus_24733
-- name    : lean_workbook_plus_24733
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/17e57903-8962-4516-a1b1-ebcc7cb3fd67
-- statement:
--   We can count how many ways there are to choose the balls without the restriction, and then just calculate how many cases violate the restriction and subtract them. Obviously, there are ${11\choose 6}$ ways to select the balls without the restriction. Now, consider the case where we select $6$ different white balls. There is only $1$ possible way for this selection. We can also select $5$ white balls and $1$ red ball. Since each ball is distinct, there are ${6 \choose 5}\cdot{5}=30$ possible selections. Finally, we can select all the red balls and $1$ white ball. There are $6$ ways to do this. Evaluating ${11\choose 6}-1-30-6$ yields $\boxed{425}$ , our answer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24733 (Nat.choose 11 6) - 1 - 30 - 6 = 425   :=  by sorry
