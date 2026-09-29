-- Prove2me | Theorems.Thm_lean_workbook_plus_7806
-- name    : lean_workbook_plus_7806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/9305cc6b-7e8b-44f9-bbb9-214aeffe0afd
-- statement:
--   Given $\sum_{cyc}a = 0$ and $\sum_{cyc}ab = \frac{3}{2}$, prove that $\sum_{cyc}a^2 = \frac{-3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7806 (a b c : ℝ) (h : a + b + c = 0) (h' : a * b + b * c + c * a = 3 / 2) : a ^ 2 + b ^ 2 + c ^ 2 = -3   :=  by sorry
