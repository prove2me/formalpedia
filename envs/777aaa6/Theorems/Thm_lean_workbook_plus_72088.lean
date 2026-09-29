-- Prove2me | Theorems.Thm_lean_workbook_plus_72088
-- name    : lean_workbook_plus_72088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/199f200d-2ab6-4b9f-b91a-db68c9a039d0
-- statement:
--   Simplify $(\\sqrt{511}+i)(\\sqrt{511}-i)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72088 : (Real.sqrt 511 + Complex.I) * (Real.sqrt 511 - Complex.I) = 512   :=  by sorry
