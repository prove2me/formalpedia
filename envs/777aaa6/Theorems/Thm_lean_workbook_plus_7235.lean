-- Prove2me | Theorems.Thm_lean_workbook_plus_7235
-- name    : lean_workbook_plus_7235
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8182e94c-49e1-45c4-9f7c-a37a64c6ae1c
-- statement:
--   Another way to look at modular arithmetic is clocks. 3 hours after 11 is 2 because $11+3=14\equiv 2\pmod {12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7235 :
  (11 + 3) % 12 = 2   :=  by sorry
