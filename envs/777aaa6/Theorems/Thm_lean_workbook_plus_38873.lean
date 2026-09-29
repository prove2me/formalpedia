-- Prove2me | Theorems.Thm_lean_workbook_plus_38873
-- name    : lean_workbook_plus_38873
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d88b9ff7-72a7-4ce5-ae8d-8fbc9eb5390a
-- statement:
--   Given $a^2 + b^2 + c^2 + d^2 = 1$, prove that $2 \geq a + b + c + d$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38873 (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : 2 ≥ a + b + c + d   :=  by sorry
