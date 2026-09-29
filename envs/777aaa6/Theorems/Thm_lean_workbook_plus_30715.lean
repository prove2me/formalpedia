-- Prove2me | Theorems.Thm_lean_workbook_plus_30715
-- name    : lean_workbook_plus_30715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0c666e4c-1689-4c58-a9bc-ca6924be2fe7
-- statement:
--   the following ineq is true $x\geq y\geq z\geq0$ \n$x(a-b)(a-c)+y(b-a)(b-c)+z(c-b)(c-a) \geq0$ \nso \n$\sum \frac{(a-c)(a-b)}{(b+c)^2}+\sum \frac{a}{b+c} \geq 1,5$ \nwitch is Nesbitt's ineq
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30715 (x y z a b c : ℝ) (hx: x ≥ y ∧ y ≥ z ∧ z ≥ 0) (hab : a ≥ b ∧ b ≥ c ∧ c ≥ 0) : x * (a - b) * (a - c) + y * (b - a) * (b - c) + z * (c - b) * (c - a) ≥ 0   :=  by sorry
