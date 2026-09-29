-- Prove2me | Theorems.Thm_lean_workbook_plus_12156
-- name    : lean_workbook_plus_12156
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d0744efd-d8aa-4265-b601-1af54b9564e2
-- statement:
--   Using the inequality which you proved in the first place, we have $2(a^2+b^2+c^2)\geq 2(ab+bc+ca)$ , yielding \n \n $2(a^2+b^2+c^2)+2(ab+bc+ca)\geq 4(ab+bc+ca)$ , but taking the reciprocal of both sides for positive real numbers $a,\ b,\ c$ , \n \n we have $\frac{1}{2(a^2+b^2+c^2)+2(ab+bc+ca)}\leq \frac{1}{4(ab+bc+ac)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12156  (a b c : ℝ) :
  2 * (a^2 + b^2 + c^2) ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
