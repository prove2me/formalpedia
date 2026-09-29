-- Prove2me | Theorems.Thm_lean_workbook_plus_77216
-- name    : lean_workbook_plus_77216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ff520d3e-594f-459b-81da-5378f3f984ca
-- statement:
--   For $a,b,c$ real positives and $a^2+b^2+c^2=1$ prove that : $\frac{a^2}{1+2bc}+\frac{b^2}{1+2ac}+\frac{c^2}{1+2ab} \geq \frac{1}{1+18abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77216 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^2 / (1 + 2 * b * c) + b^2 / (1 + 2 * a * c) + c^2 / (1 + 2 * a * b) ≥ 1 / (1 + 18 * a * b * c)   :=  by sorry
