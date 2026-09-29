-- Prove2me | Theorems.Thm_lean_workbook_plus_9114
-- name    : lean_workbook_plus_9114
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a9507b9d-208e-4bb8-9c73-a91d7f8390eb
-- statement:
--   Prove that $(a + b + c)^2 \ge 3(ab + bc + ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9114 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
