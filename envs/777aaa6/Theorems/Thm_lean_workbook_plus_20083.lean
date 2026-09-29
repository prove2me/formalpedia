-- Prove2me | Theorems.Thm_lean_workbook_plus_20083
-- name    : lean_workbook_plus_20083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/13efe50b-1192-46af-aff7-221edb5e1154
-- statement:
--   Prove $(a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2)\ge (a^2b+b^2c+c^2a)(ab^2+bc^2+ca^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20083 (a b c : ℝ) : (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2)   :=  by sorry
