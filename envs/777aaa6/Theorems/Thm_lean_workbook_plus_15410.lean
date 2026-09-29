-- Prove2me | Theorems.Thm_lean_workbook_plus_15410
-- name    : lean_workbook_plus_15410
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ffcc5fbb-f61d-4b0c-992a-46ffe6704338
-- statement:
--   If $2a^6-2a^4+a^2=\frac{3}{2}$, $a \in R$, then prove that $a^8>1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15410 (a : ℝ) (h : 2*a^6 - 2*a^4 + a^2 = 3/2) : a^8 > 1   :=  by sorry
