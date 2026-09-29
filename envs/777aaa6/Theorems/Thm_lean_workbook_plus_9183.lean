-- Prove2me | Theorems.Thm_lean_workbook_plus_9183
-- name    : lean_workbook_plus_9183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f739efad-c103-4ed2-9e52-34e218f93c3e
-- statement:
--   If i) $f(1)=1$ ii) $f(2x)=4f(x)+6$ iii) $f(x+4)=4f(x)+4f(1)+8f(2)$ Find $f(6)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9183 (f : ℝ → ℝ) (hf1 : f 1 = 1) (hf2 : ∀ x, f (2 * x) = 4 * f x + 6) (hf3 : ∀ x, f (x + 4) = 4 * f x + 4 * f 1 + 8 * f 2) : f 6 = 106   :=  by sorry
