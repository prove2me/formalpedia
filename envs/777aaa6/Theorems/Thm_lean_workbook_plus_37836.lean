-- Prove2me | Theorems.Thm_lean_workbook_plus_37836
-- name    : lean_workbook_plus_37836
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/549dcf24-a4ee-4493-9d22-9efb9ed793ff
-- statement:
--   Determine the last digit of number $18^1+18^2+...+18^{19}+18^{20}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37836 : (∑ k in Finset.Icc 1 20, 18^k) % 10 = 8   :=  by sorry
