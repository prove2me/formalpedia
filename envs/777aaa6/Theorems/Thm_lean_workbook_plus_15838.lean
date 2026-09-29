-- Prove2me | Theorems.Thm_lean_workbook_plus_15838
-- name    : lean_workbook_plus_15838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1f25902e-96f3-4d0c-a287-7400038a311b
-- statement:
--   Prove that $a^2+b^2+c^2+d^2\ge ab+bc+cd+da$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15838 (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * b + b * c + c * d + d * a   :=  by sorry
