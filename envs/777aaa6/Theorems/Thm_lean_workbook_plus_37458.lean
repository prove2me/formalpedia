-- Prove2me | Theorems.Thm_lean_workbook_plus_37458
-- name    : lean_workbook_plus_37458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/32eba8d4-c3f8-4074-b09f-6fb29c243330
-- statement:
--   Prove $x^2+y^2+z^2+3xy-xz-yz\geq 4xy$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37458 (x y z : ℝ) : x^2 + y^2 + z^2 + 3 * x * y - x * z - y * z ≥ 4 * x * y   :=  by sorry
