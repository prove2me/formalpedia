-- Prove2me | Theorems.Thm_lean_workbook_plus_14832
-- name    : lean_workbook_plus_14832
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3145de42-49ac-498c-9d43-18ffc3fd270a
-- statement:
--   Question NO. 2 \nIf $a,b,c \in \mathbb{R^+}$ , prove that \n $$\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \geq \frac{(a+b+c)^2}{ab+bc+ca}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14832 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (a + b + c) ^ 2 / (a * b + b * c + c * a)   :=  by sorry
