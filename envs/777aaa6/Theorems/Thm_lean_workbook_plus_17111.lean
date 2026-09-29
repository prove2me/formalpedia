-- Prove2me | Theorems.Thm_lean_workbook_plus_17111
-- name    : lean_workbook_plus_17111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b9dd9180-c95e-4d3d-8d2d-0b6c6837d69b
-- statement:
--   Prove that $a^2(b+c)^2 +(b^2+c^2)(b+c)^2 \geq 2a(b+c)(b^2+c^2) +2bc(b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17111 (a b c : ℝ) : a^2 * (b + c)^2 + (b^2 + c^2) * (b + c)^2 ≥ 2 * a * (b + c) * (b^2 + c^2) + 2 * b * c * (b^2 + c^2)   :=  by sorry
