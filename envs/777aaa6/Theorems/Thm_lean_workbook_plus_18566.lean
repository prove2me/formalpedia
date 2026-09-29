-- Prove2me | Theorems.Thm_lean_workbook_plus_18566
-- name    : lean_workbook_plus_18566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/52905746-a73f-4bd2-b680-1879da115f4c
-- statement:
--   Given that $a, b, c, d$ are reals such that $a+b+c+d=0 \ ab+bc+cd+da=0 \ ab+ac+ad+bc+bd+cd=0 \ a^3+b^3+c^3+d^3=0$ prove that $a=b=c=d=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18566 (a b c d : ℝ) (h1 : a+b+c+d=0) (h2 : a*b+b*c+c*d+d*a=0) (h3 : a*b + a*c + a*d + b*c + b*d + c*d=0) (h4 : a^3+b^3+c^3+d^3=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0   :=  by sorry
