-- Prove2me | Theorems.Thm_lean_workbook_plus_35226
-- name    : lean_workbook_plus_35226
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/12d966bf-7cb4-4d58-9de0-b1ad8e126a85
-- statement:
--   \(\frac{1}{2} = \frac{{\sin ^2 x + \cos ^2 x}}{2} > \sin x\cos x\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35226 : ∀ x : ℝ, 1 / 2 = (sin x ^ 2 + cos x ^ 2) / 2 ∧ (sin x ^ 2 + cos x ^ 2) / 2 > sin x * cos x   :=  by sorry
