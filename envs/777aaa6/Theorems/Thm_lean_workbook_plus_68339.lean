-- Prove2me | Theorems.Thm_lean_workbook_plus_68339
-- name    : lean_workbook_plus_68339
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c053b09f-0a21-412d-8f6a-92f4e487a10c
-- statement:
--   Let $a>1,b>1$ , prove that \n $\frac{a^2}{b-1}+\frac{b^2}{a-1}\ge 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68339 (a b : ℝ) (ha : a > 1) (hb : b > 1) : (a^2 / (b - 1) + b^2 / (a - 1)) ≥ 8   :=  by sorry
