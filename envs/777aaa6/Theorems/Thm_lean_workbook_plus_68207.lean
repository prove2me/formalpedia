-- Prove2me | Theorems.Thm_lean_workbook_plus_68207
-- name    : lean_workbook_plus_68207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/327162e6-506d-482f-b7f7-109d62c05372
-- statement:
--   Let $a,b,c$ be reals.Then \n\n $$(a^2+1)(b^2+1)(c^2+1)\geqslant (a+b)(b+c)(c+a) +\frac{1}{3} (ab+bc+ca-a-b-c)^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68207 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + b) * (b + c) * (c + a) + (1 / 3) * (a * b + b * c + c * a - a - b - c)^2   :=  by sorry
