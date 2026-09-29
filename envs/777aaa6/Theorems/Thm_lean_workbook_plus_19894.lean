-- Prove2me | Theorems.Thm_lean_workbook_plus_19894
-- name    : lean_workbook_plus_19894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bd2aec5e-8fee-4d70-9d96-05cb89d74955
-- statement:
--   Prove that for $x+y+z+w=2$, $(x+z)(y+w)\le 1$ using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19894 (x y z w : ℝ) (h : x + y + z + w = 2) :
  (x + z) * (y + w) ≤ 1   :=  by sorry
