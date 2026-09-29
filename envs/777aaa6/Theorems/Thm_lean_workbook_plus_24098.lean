-- Prove2me | Theorems.Thm_lean_workbook_plus_24098
-- name    : lean_workbook_plus_24098
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/014dd290-7f9f-414d-ae8d-af5f32e87247
-- statement:
--   Given $x^3998=0$ or $x=i, -i, 1$, find $x^{4002}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24098 (x : ℂ) (hx : x^3998 = 0) : x^4002 = 0   :=  by sorry
