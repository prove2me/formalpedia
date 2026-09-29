-- Prove2me | Theorems.Thm_lean_workbook_plus_14177
-- name    : lean_workbook_plus_14177
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b1f6ce92-632d-4615-a245-c0b183ce807a
-- statement:
--   Prove that \\( e^{-i\theta} = \cos \theta - i\sin \theta \\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14177 : ∀ θ : ℝ, exp (-I*θ) = cos θ - I * sin θ   :=  by sorry
