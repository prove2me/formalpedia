-- Prove2me | Theorems.Thm_lean_workbook_plus_57173
-- name    : lean_workbook_plus_57173
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9ba22c0a-8c3d-49bb-9c86-dccaeb15b060
-- statement:
--   Prove that\n \(a^2+b^2+c^2+d^2+abcd+1\ge(ab+ac+ad+bc+bd+cd)\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57173 : ∀ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 + a * b * c * d + 1 ≥ a * b + a * c + a * d + b * c + b * d + c * d   :=  by sorry
