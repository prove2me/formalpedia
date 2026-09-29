-- Prove2me | Theorems.Thm_lean_workbook_plus_61599
-- name    : lean_workbook_plus_61599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/90a9cdc3-4922-4670-9c67-342e9318d5a1
-- statement:
--   (Proof) For all $x,y,z$ we have $(x-z)^2\le 2((x-y)^2+(y-z)^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61599 (x y z : ℝ) : (x - z) ^ 2 ≤ 2 * ((x - y) ^ 2 + (y - z) ^ 2)   :=  by sorry
