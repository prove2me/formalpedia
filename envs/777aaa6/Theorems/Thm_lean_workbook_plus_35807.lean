-- Prove2me | Theorems.Thm_lean_workbook_plus_35807
-- name    : lean_workbook_plus_35807
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/efe45049-3738-4a36-b9b2-74f919c139ee
-- statement:
--   Expand $(x+1)(y+1)(z+1)$ and see if it looks familiar.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35807 : (x+1)*(y+1)*(z+1) = x*y*z + x*y + x*z + y*z + x + y + z + 1   :=  by sorry
