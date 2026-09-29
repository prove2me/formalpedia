-- Prove2me | Theorems.Thm_lean_workbook_plus_64657
-- name    : lean_workbook_plus_64657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3c5a5ad5-e19e-4a36-a91c-915e3763b4d0
-- statement:
--   First equation is $(x-\\sqrt 3)^3=64$ and so, assuming we are speaking of real numbers, $x=4+\\sqrt 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64657 (x : ℝ) (hx : (x - Real.sqrt 3)^3 = 64) : x = 4 + Real.sqrt 3   :=  by sorry
