-- Prove2me | Theorems.Thm_lean_workbook_plus_33318
-- name    : lean_workbook_plus_33318
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f4cd6822-da26-45e4-ae10-7e06a6394674
-- statement:
--   If $ a,b,c\in\mathbb{R}$ , prove that $ (a^2+b^2+c^2)^2 \ge a^3b + b^3c + c^3a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33318 (a b c : ℝ) : (a^2 + b^2 + c^2)^2 ≥ a^3 * b + b^3 * c + c^3 * a   :=  by sorry
