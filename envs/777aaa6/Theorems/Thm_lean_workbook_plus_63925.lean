-- Prove2me | Theorems.Thm_lean_workbook_plus_63925
-- name    : lean_workbook_plus_63925
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9401b257-fa90-44c1-a6e0-eeb8f8e1ca22
-- statement:
--   Is the calculation ${11 \choose 4} {7 \choose 5} = 6930$ correct?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63925 :
  (Nat.choose 11 4 * Nat.choose 7 5) = 6930   :=  by sorry
