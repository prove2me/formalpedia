-- Prove2me | Theorems.Thm_lean_workbook_plus_52330
-- name    : lean_workbook_plus_52330
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/f41f7c39-34b8-421a-b27e-6d76280ef533
-- statement:
--   Let $ X, Y, Z$ be independent random variables uniformly distributed on the unit interval $ [0,1]$ . Prove that $ (XY)^Z$ is also uniformly distributed (yes, I didn't believe it either).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52330 (X Y Z : ℝ) (hx : X ∈ Set.Icc 0 1) (hy : Y ∈ Set.Icc 0 1) (hz : Z ∈ Set.Icc 0 1) : (X * Y) ^ Z ∈ Set.Icc 0 1   :=  by sorry
