-- Prove2me | Theorems.Thm_lean_workbook_plus_63473
-- name    : lean_workbook_plus_63473
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a66a54b2-e541-46ac-9fac-0b214e3144ff
-- statement:
--   Given $a, b, c$ as the lengths of sides $BC, AC, AB$ respectively, prove that $\frac{1}{4}(b^2 + c^2) \geq \frac{1}{2}bc$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63473 (a b c : ℝ) (hx: a + b > c) (hb : a + c > b) (hc : b + c > a) : 1 / 4 * (b ^ 2 + c ^ 2) ≥ 1 / 2 * b * c   :=  by sorry
