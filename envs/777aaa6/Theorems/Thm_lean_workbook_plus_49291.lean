-- Prove2me | Theorems.Thm_lean_workbook_plus_49291
-- name    : lean_workbook_plus_49291
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/21615dc2-5f53-436c-9b2e-0559f4790b6e
-- statement:
--   Solve for $x$ and $y$ in the equation $a-\sqrt{a^2-1}=x+y-2\sqrt{xy}$ given $a=x+y$ and $a^2-1=4xy$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49291 (a x y : ℝ) (ha : a = x + y) (hb : a^2 - 1 = 4 * x * y) : a - Real.sqrt (a^2 - 1) = x + y - 2 * Real.sqrt (x * y)   :=  by sorry
