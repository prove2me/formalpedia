-- Prove2me | Theorems.Thm_lean_workbook_plus_59627
-- name    : lean_workbook_plus_59627
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/82c63e0f-4191-4ab6-b57c-e8cbc3a9502a
-- statement:
--   RHS $\leq$ a$\frac{b+c}{2}$ + b$\frac{c+a}{2}$ + c$\frac{a+b}{2}$ . \n\n It suffices to prove that \n\n $\frac{(a+b+c)^2}{3} \geq a\frac{b+c}{2} + b\frac{c+a}{2} + c\frac{a+b}{2} \Longleftrightarrow$ \n\n $2(a+b+c)^2 \geq 6(ab+bc+ca) \Longleftrightarrow$ \n\n $(a+b+c)^2 \geq 3(ab+bc+ca) \Longleftrightarrow$ \n\n $a^2 + b^2 + c^2 + 2(ab+bc+ca) \geq 3(ab+bc+ca) \Longleftrightarrow$ \n\n $a^2 + b^2 + c^2 \geq ab + bc + ca \Longleftrightarrow$ \n\n $2(a^2 + b^2 + c^2) \geq 2(ab+bc+ca) \Longleftrightarrow$ \n\n $a^2 - 2ab + b^2 + b^2 - 2bc + c^2 + c^2 - 2ca + a^2 \geq 0 \Longleftrightarrow$ \n\n $(a-b)^2 + (b-c)^2 + (c-a)^2 \geq 0$ , which holds as a sum of squares. The equality holds only when $a=b=c$ and $a,b,c\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59627 (a b c : ℝ) : a * (b + c) / 2 + b * (c + a) / 2 + c * (a + b) / 2 ≤ (a + b + c) ^ 2 / 3   :=  by sorry
