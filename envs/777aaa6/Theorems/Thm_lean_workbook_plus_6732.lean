-- Prove2me | Theorems.Thm_lean_workbook_plus_6732
-- name    : lean_workbook_plus_6732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/717e2e5f-62ee-48cd-b758-a2d58bc46194
-- statement:
--   Let the function $f(x)=3x+6,$ if $x<5$ and $f(x)=7x-20,$ if $x\geq 5.$ Then find the value of $f(f(f(2))).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6732 (f : ℝ → ℝ) (f_def : ∀ x, x < 5 → f x = 3 * x + 6 ∧ ∀ x, 5 ≤ x → f x = 7 * x - 20) : f (f (f 2)) = 428   :=  by sorry
