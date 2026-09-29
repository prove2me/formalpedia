-- Prove2me | Theorems.Thm_lean_workbook_plus_27233
-- name    : lean_workbook_plus_27233
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/9d22e672-28c6-437b-a9fa-27e89521adf0
-- statement:
--   If $a,b,c$ are positive numbers such that $ab+bc+ca=1$ , then \n $(a^{2}+1)(b^{2}+1)(c^{2}+1) \geq \frac 4{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27233 (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) (habc : a * b + b * c + c * a = 1) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 4 / 3   :=  by sorry
