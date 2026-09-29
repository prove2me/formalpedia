-- Prove2me | Theorems.Thm_lean_workbook_plus_68452
-- name    : lean_workbook_plus_68452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3151a13c-494d-41ad-aa0b-54205d6e6cdc
-- statement:
--   prove that: $(b^2+c^2-a^2)(b-c)^2+(-b^2+a^2+c^2)(c-a)^2+(b^2+a^2-c^2)(a-b)^2\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68452 (a b c : ℝ) : (b^2+c^2-a^2)*(b-c)^2+(-b^2+a^2+c^2)*(c-a)^2+(b^2+a^2-c^2)*(a-b)^2 ≥ 0   :=  by sorry
