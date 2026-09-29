-- Prove2me | Theorems.Thm_lean_workbook_plus_3908
-- name    : lean_workbook_plus_3908
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/82ac7d46-3d48-4488-a681-5b031eed2e21
-- statement:
--   Prove that $x^2 \le 3x-2$ for $x \in [1,2]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3908 (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 2) : x^2 ≤ 3*x - 2   :=  by sorry
