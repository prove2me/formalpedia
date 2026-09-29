-- Prove2me | Theorems.Thm_lean_workbook_plus_54867
-- name    : lean_workbook_plus_54867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/63f8b4c8-3a81-4949-9dd2-a8356aa07b6e
-- statement:
--   Prove $(27-B)(12B-27)\geq 9(4B^{2}+11B-45)$ for $2.25<B\leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54867 (B : ℝ) (hB : 2.25 < B ∧ B ≤ 3) :
  (27 - B) * (12 * B - 27) ≥ 9 * (4 * B ^ 2 + 11 * B - 45)   :=  by sorry
