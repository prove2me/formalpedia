-- Prove2me | Theorems.Thm_lean_workbook_plus_54522
-- name    : lean_workbook_plus_54522
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/284dbf20-c77c-4ff6-be6b-ee4105ac47e4
-- statement:
--   Question NO. 2 \nIf $a,b,c \in \mathbb{R^+}$ , prove that \n $$\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \geq \frac{(a+b+c)^2}{ab+bc+ca}$$ \n\njust Cauchy-Schwartz...\n\nI know so I wrote easy ones!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54522 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (a + b + c) ^ 2 / (a * b + b * c + a * c)   :=  by sorry
