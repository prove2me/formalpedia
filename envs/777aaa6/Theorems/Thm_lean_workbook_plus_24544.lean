-- Prove2me | Theorems.Thm_lean_workbook_plus_24544
-- name    : lean_workbook_plus_24544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/de258933-dc47-4430-894c-52fd9aa61a04
-- statement:
--   prove that: \n $ (a^2c + b^2a + c^2b - a^2b - b^2c - c^2a) = (b - a)(c - a)(c - b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24544 (a b c : ℂ) :
  (a^2*c + b^2*a + c^2*b - a^2*b - b^2*c - c^2*a) = (b - a)*(c - a)*(c - b)   :=  by sorry
