-- Prove2me | Theorems.Thm_lean_workbook_plus_32081
-- name    : lean_workbook_plus_32081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a9793009-68e8-405b-a9b7-a9bbcdb60383
-- statement:
--   x^5 + \frac {1}{x^5} + 10(4) + 5(52) = 1024 \implies x^5 + \frac {1}{x^5} = \boxed{724}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32081 (x : ℝ) (hx : x^5 + 1/x^5 + 10*4 + 5*52 = 1024) : x^5 + 1/x^5 = 724   :=  by sorry
