-- Prove2me | Theorems.Thm_lean_workbook_plus_35153
-- name    : lean_workbook_plus_35153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/d4289c07-780d-4b43-a444-814fafb27cc5
-- statement:
--   Calling the four numbers a, b, c, d, we have the equations:\n\n $\frac{a+b+c}{3} + d = 89 \rightarrow a+b+c+3d = 267$ \n $\frac{b+c+d}{3} + a = 95 \rightarrow b+c+d+3a = 285$ \n $\frac{c+d+a}{3} + b = 101 \rightarrow c+d+a+3b = 303$ \n $\frac{d+a+b}{3} + c = 117 \rightarrow d+a+b+3c = 351$ \n\nAdding all four equations together:\n\n $6(a+b+c+d) = 1206$ \n $a+b+c+d = 201$ \n\nPlugging this value into each of the four equations, d = 33, a=42, b=51, c=75
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35153 (a b c d : ℕ) : (a+b+c)/3 + d = 89 ∧ (b+c+d)/3 + a = 95 ∧ (c+d+a)/3 + b = 101 ∧ (d+a+b)/3 + c = 117 ↔ d = 33 ∧ a = 42 ∧ b = 51 ∧ c = 75   :=  by sorry
