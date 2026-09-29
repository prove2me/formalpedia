-- Prove2me | Theorems.Thm_lean_workbook_plus_3625
-- name    : lean_workbook_plus_3625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/50c48e35-5fe2-43a4-b020-a7e842873693
-- statement:
--   To have the solution $x=0$ only, $1-2r\ge0,\ r\le\tfrac12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3625 (r : ℝ) : (1 - 2 * r ≥ 0 ∧ r ≤ 1 / 2) ↔ r ≤ 1 / 2   :=  by sorry
