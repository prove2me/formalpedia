-- Prove2me | Theorems.Thm_lean_workbook_plus_6211
-- name    : lean_workbook_plus_6211
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/49c09935-1e1d-42da-ac9e-307c33e5a3c1
-- statement:
--   prove $ \frac{a}{1+bc}+\frac{b}{1+ca}+\frac{c}{1+ab}+abc \leq \frac{5}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6211 : ∀ a b c : ℝ, (a / (1 + b * c) + b / (1 + c * a) + c / (1 + a * b) + a * b * c ≤ 5 / 2)   :=  by sorry
