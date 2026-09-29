-- Prove2me | Theorems.Thm_lean_workbook_plus_43985
-- name    : lean_workbook_plus_43985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/db8524b4-5cb7-45c6-807f-d9850a703fb8
-- statement:
--   Let $a,b,c>0$ Prove that: $ \frac{a^2-b^2}{b+c }+ \frac{b^2-c^2}{c+a } \geq \frac{a^2-c^2}{a+b } $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43985 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b^2) / (b + c) + (b^2 - c^2) / (c + a) ≥ (a^2 - c^2) / (a + b)   :=  by sorry
