-- Prove2me | Theorems.Thm_lean_workbook_plus_74708
-- name    : lean_workbook_plus_74708
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/70e94005-0fe4-4bfb-9d0a-d86cc3dfb48f
-- statement:
--   Given $f(x+y)+f(x-y)=2(f(x)+f(y))$, show that $f(0)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74708 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) + f (x - y) = 2 * (f x + f y)) : f 0 = 0   :=  by sorry
