-- Prove2me | Theorems.Thm_lean_workbook_plus_47112
-- name    : lean_workbook_plus_47112
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0f32e69a-df17-4420-b143-4c6b1a98d802
-- statement:
--   $2, \dfrac{a^2+b^2+c^2}{ab+bc+ca}\geq \dfrac{2}{3}(\dfrac{a}{b+c}+\dfrac{b}{c+a}+\dfrac{c}{a+b}).$ $\iff$ \n $\dfrac{a^2+b^2+c^2}{ab+bc+ca}+2\geq \dfrac{2}{3}(\dfrac{a}{b+c}+1+\dfrac{b}{c+a}+1+\dfrac{c}{a+b}+1).$ $\iff$ \n $\dfrac{(a+b+c)^2}{ab+bc+ca}\geq \dfrac{2}{3}(\dfrac{a+b+c}{b+c}+\dfrac{a+b+c}{c+a}+\dfrac{a+b+c}{a+b}).$ $\iff$ \n $\dfrac{a+b+c}{ab+bc+ca}\geq \dfrac{2}{3}(\dfrac{1}{b+c}+\dfrac{1}{c+a}+\dfrac{1}{a+b}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47112 : ∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 2 ≥ (2 / 3) * (a / (b + c) + b / (c + a) + c / (a + b))   :=  by sorry
