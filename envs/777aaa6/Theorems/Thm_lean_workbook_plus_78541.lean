-- Prove2me | Theorems.Thm_lean_workbook_plus_78541
-- name    : lean_workbook_plus_78541
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d5aa82a0-a825-47f8-a5ed-1fbc398c35ec
-- statement:
--   Prove that $a^2 + b^2 + c^2 \geq ab + bc + ca$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78541 {a b c : ℝ} : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
