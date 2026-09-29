-- Prove2me | Theorems.Thm_lean_workbook_plus_48431
-- name    : lean_workbook_plus_48431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5c04f911-ab4b-4a66-b7b8-1a1499c64a70
-- statement:
--   Prove that for a,b,c,d $\in$ R suh that a<b<c<d $(a+b+c+d)^2$ >=8(ac+bd)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48431 (a b c d : ℝ) (h1 : a < b ∧ b < c ∧ c < d) : (a + b + c + d) ^ 2 ≥ 8 * (a * c + b * d)   :=  by sorry
