-- Prove2me | Theorems.Thm_lean_workbook_plus_20623
-- name    : lean_workbook_plus_20623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/44d10b2a-c900-44d4-a4d2-84df66a25f64
-- statement:
--   If $a\geq -b$ , then $-a\leq b$ , combining this with $b\leq a$ you get $-a\leq b\leq a$ , i.e. $a\geq |b|$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20623  (a b : ℝ)
  (h₀ : -b ≤ a)
  (h₁ : b ≤ a) :
  a ≥ |b|   :=  by sorry
