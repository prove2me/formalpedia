-- Prove2me | Theorems.Thm_lean_workbook_plus_15818
-- name    : lean_workbook_plus_15818
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5c569a1b-c3ed-4672-8f6c-f5712ea987c0
-- statement:
--   By triangle inequality we have \n $$ | \sin {x} +\ cos{x} | +| \sin{x} -\cos{x}| \ge | \sin {x}+\cos{x} +\sin{x}-\cos{x}|=2|\sin{x} |\ge 2\sin ^2 {x} $$ equality holds if and only if $x=\dfrac {\pi} {2}$ or $x=\dfrac {3\pi} {2} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15818 :
  ∀ x : ℝ,
    abs (sin x + cos x) + abs (sin x - cos x) ≥ 2 * (sin x)^2   :=  by sorry
