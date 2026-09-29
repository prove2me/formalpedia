-- Prove2me | Theorems.Thm_lean_workbook_plus_76404
-- name    : lean_workbook_plus_76404
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e1ade880-e68b-48c6-8428-5e2ee16ed87c
-- statement:
--   If $x+y=\frac {5}{2}$ , and $x^2 + y^2 = \frac {13}{4}$ , what is the value of $x^5 + y^5$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76404 (x y : ℝ) (h₁ : x + y = 5/2) (h₂ : x^2 + y^2 = 13/4) : x^5 + y^5 = 275/32   :=  by sorry
