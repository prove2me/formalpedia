-- Prove2me | Theorems.Thm_lean_workbook_plus_51375
-- name    : lean_workbook_plus_51375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/70d4d8f3-5c1e-4236-86c4-10cf2c67947b
-- statement:
--   Explain the process of getting from $(a-9)(a+3)=0$ to a-9=0 (==) a=9 or a+3=0 (==) a=-3
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51375 (a : ℝ) : (a - 9) * (a + 3) = 0 ↔ a - 9 = 0 ∨ a + 3 = 0   :=  by sorry
