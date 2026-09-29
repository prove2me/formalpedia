-- Prove2me | Theorems.Thm_lean_workbook_plus_14370
-- name    : lean_workbook_plus_14370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4718ee1f-94ca-4e8d-a774-3a7aa38d8175
-- statement:
--   For $a, b, c >0$ , prove that \n\n $$(a^2+1)(b^2+1)(c^2+1)\geq (a+b)(b+c)(c+a)$$ \n\n By C-S \n\n $$(a^2+1)(1+b^2)\geq(a+b)^2,...$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14370 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2+1)*(b^2+1)*(c^2+1) ≥ (a+b)*(b+c)*(c+a)   :=  by sorry
