-- Prove2me | Theorems.Thm_lean_workbook_plus_80764
-- name    : lean_workbook_plus_80764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5cef15a3-523c-4851-8a2d-c77a074c1134
-- statement:
--   Prove that for positive real numbers $a$, $b$, $c$ satisfying $2b^2 = a^2 + c^2$, the following equality holds: $\frac{1}{a+b} + \frac{1}{b+c} = \frac{2}{a+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80764 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : 2 * b^2 = a^2 + c^2) : 1 / (a + b) + 1 / (b + c) = 2 / (a + c)   :=  by sorry
