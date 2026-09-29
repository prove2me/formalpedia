-- Prove2me | Theorems.Thm_lean_workbook_plus_38504
-- name    : lean_workbook_plus_38504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b01bd1b4-a489-4538-85cb-e6e871b3cf1c
-- statement:
--   $ \sum_{cyc}(a - b)^2\geq0$ is true
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38504 {a b c : ℝ} : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0   :=  by sorry
