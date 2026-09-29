-- Prove2me | Theorems.Thm_lean_workbook_plus_27330
-- name    : lean_workbook_plus_27330
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/189375ca-574b-4db2-b079-57d4121685c9
-- statement:
--   Let $a,b,c$ be reals. $(1+a^2)(1+b^2)(1+c^2)\ge(1+ ab)(1+bc )(1+ca )$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27330 ∀ a b c : ℝ, (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ (1 + a * b) * (1 + b * c) * (1 + c * a)   :=  by sorry
