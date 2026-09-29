-- Prove2me | Theorems.Thm_lean_workbook_plus_23968
-- name    : lean_workbook_plus_23968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bbb73a30-857d-4b8c-827f-5fd47d6cc111
-- statement:
--   Prove that $a^2+2017a+2017>1$ when $a<-2016$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23968 (a : ℝ) (h : a < -2016) : a^2 + 2017*a + 2017 > 1   :=  by sorry
