-- Prove2me | Theorems.Thm_WorkbookSource_plus_76043
-- name    : WorkbookSource.plus_76043
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:11:01.819013+00:00
-- url     : https://prove2.me/theorems/3b2643cb-f6e7-4f2f-99cc-fde32c6be2b4
-- title:
--   A piecewise function has no fixed point
-- statement:
--   Prove that if $f(x) = \begin{cases}1, & 0\le x \le 1/2,\\0, & 1/2 < x \le 1\end{cases}$, it does not have a fixed point in $[0,1]$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76043` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76043; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76043 (f : ℝ → ℝ) (hf: f = fun x => if x ≤ 1/2 then 1 else 0) : ¬ (∃ x, f x = x)   :=  by sorry
