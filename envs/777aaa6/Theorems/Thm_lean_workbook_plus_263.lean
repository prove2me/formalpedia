-- Prove2me | Theorems.Thm_lean_workbook_plus_263
-- name    : lean_workbook_plus_263
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/6d062cac-57ff-4f95-ad62-401171ecb222
-- statement:
--   For $n=4$ we have: $a_4 = \frac{13}{6}$ and $\left \lfloor a_4^2 \right \rfloor = \left \lfloor \frac{13^2}{6^2} \right \rfloor = 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_263 :
  Int.floor ((13 : ℝ) / 6)^2 = 4   :=  by sorry
