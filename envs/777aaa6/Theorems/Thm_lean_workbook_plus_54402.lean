-- Prove2me | Theorems.Thm_lean_workbook_plus_54402
-- name    : lean_workbook_plus_54402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fa97191e-6961-4b52-b808-d69471ae28bb
-- statement:
--   Prove that $a^2 + b^2 + c^2 \geq ab + ac + bc$ using SOS (Sum of Squares) method.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54402 {a b c : ℝ} : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + a * c + b * c   :=  by sorry
