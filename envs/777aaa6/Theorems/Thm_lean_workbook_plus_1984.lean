-- Prove2me | Theorems.Thm_lean_workbook_plus_1984
-- name    : lean_workbook_plus_1984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0109e87f-c33e-4354-bf5d-f49fc8b9c76f
-- statement:
--   Now, $(c-a)(c-b)=c^2-ac-bc+ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1984 (a b c : ℂ) : (c - a) * (c - b) = c^2 - a*c - b*c + a*b   :=  by sorry
