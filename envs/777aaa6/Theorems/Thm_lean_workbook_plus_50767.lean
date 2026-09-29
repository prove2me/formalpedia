-- Prove2me | Theorems.Thm_lean_workbook_plus_50767
-- name    : lean_workbook_plus_50767
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/bf7f3f71-5e01-42cb-a5c4-02d586b6ebee
-- statement:
--   I think, $3abc(a+b+c)\le (ab+bc+ca)^{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50767 (a b c : ℝ) : 3 * a * b * c * (a + b + c) ≤ (a * b + b * c + c * a) ^ 2   :=  by sorry
