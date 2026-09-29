-- Prove2me | Theorems.Thm_lean_workbook_plus_51137
-- name    : lean_workbook_plus_51137
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/282a386b-c22f-4b48-b953-b5cc8243cad7
-- statement:
--   Prove that $(a^2+b^2+c^2)^2 \geq (ab+bc+ca)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51137 (a b c : ℝ) : (a^2+b^2+c^2)^2 ≥ (a * b + b * c + c * a)^2   :=  by sorry
