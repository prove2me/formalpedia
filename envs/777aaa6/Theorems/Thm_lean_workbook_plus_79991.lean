-- Prove2me | Theorems.Thm_lean_workbook_plus_79991
-- name    : lean_workbook_plus_79991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/feeb3b87-f582-4464-a30d-6ea1a990eefa
-- statement:
--   If $a^2-3a+1=0$ , find the value of $\frac{a^3}{a^6+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79991 (a : ℝ) (ha : a^2 - 3*a + 1 = 0) : a^3/(a^6 + 1) = 1/18   :=  by sorry
