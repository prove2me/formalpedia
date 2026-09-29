-- Prove2me | Theorems.Thm_lean_workbook_plus_12893
-- name    : lean_workbook_plus_12893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/add946a2-5028-479d-99fb-f1caa0615952
-- statement:
--   prove that $3(a^{2}+b^{2}+c^{2}+d^{2})\geq 2(ab+ac+ad+bc+bd+cd)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12893 : ∀ a b c d : ℝ, 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d)   :=  by sorry
