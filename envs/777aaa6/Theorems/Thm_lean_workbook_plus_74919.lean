-- Prove2me | Theorems.Thm_lean_workbook_plus_74919
-- name    : lean_workbook_plus_74919
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/8311f927-1b8f-4679-bafd-4df91958b90b
-- statement:
--   Show that the product of connected spaces, $[0,1]$ and $(0,1)$, is connected.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74919 : IsConnected (Set.Icc 0 1 ×ˢ Set.Ioo 0 1)   :=  by sorry
