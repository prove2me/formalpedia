-- Prove2me | Theorems.Thm_lean_workbook_plus_59114
-- name    : lean_workbook_plus_59114
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/dd1c4f1a-7680-430f-a977-66ee13a3306e
-- statement:
--   Suppose $f(2x+m)=2f(x)+u$ . Then if $t(x)=f(x-m)+u$ then $t(2x)=2t(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59114 (f : ℝ → ℝ) (u m : ℝ) (t : ℝ → ℝ) (hf : ∀ x, f (2 * x + m) = 2 * f x + u) (ht : ∀ x, t x = f (x - m) + u) : ∀ x, t (2 * x) = 2 * t x   :=  by sorry
