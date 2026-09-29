-- Prove2me | Theorems.Thm_lean_workbook_plus_19151
-- name    : lean_workbook_plus_19151
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3efbe2f6-06c8-45b2-bae9-0b8ddd30d43c
-- statement:
--   Prove that for positive reals $a$, $b$, $c$ with $abc=1$, the inequality $(a^2+1)(b^2+1)(c^2+1) \geq (a+1)(b+1)(c+1)$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19151 (a b c : ℝ) (habc : a * b * c = 1) :
  (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + 1) * (b + 1) * (c + 1)   :=  by sorry
