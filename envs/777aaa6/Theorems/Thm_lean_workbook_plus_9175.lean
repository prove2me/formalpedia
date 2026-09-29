-- Prove2me | Theorems.Thm_lean_workbook_plus_9175
-- name    : lean_workbook_plus_9175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/48d63905-6bdb-4ed1-8904-71a8d9513575
-- statement:
--   (*) Prove that \(a^2+b^2+c^2\geq ab+ac+bc\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9175 (a b c: ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + a * c + b * c   :=  by sorry
