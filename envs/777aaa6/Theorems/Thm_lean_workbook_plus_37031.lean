-- Prove2me | Theorems.Thm_lean_workbook_plus_37031
-- name    : lean_workbook_plus_37031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8a812f7a-4831-41b2-9b8e-fdb0283f0ddb
-- statement:
--   Prove that the sum of non-negative terms $(b - \frac {a}{2})^2 + (c - \frac {a}{2})^2 + (d - \frac {a}{2})^2 + (e - \frac {a}{2})^2$ is greater than or equal to 0
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37031 (a b c d e : ℝ) : (b - a/2)^2 + (c - a/2)^2 + (d - a/2)^2 + (e - a/2)^2 ≥ 0   :=  by sorry
