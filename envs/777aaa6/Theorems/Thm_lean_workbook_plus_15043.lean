-- Prove2me | Theorems.Thm_lean_workbook_plus_15043
-- name    : lean_workbook_plus_15043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e9882c7d-7bfa-42f6-8883-5bef3fe3169a
-- statement:
--   If $a,b>0$ , $\frac{1}{a^2+1}+\frac{1}{b^2+1}=1$ .Then $ab=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15043 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (a^2 + 1) + 1 / (b^2 + 1) = 1 ↔ a * b = 1   :=  by sorry
