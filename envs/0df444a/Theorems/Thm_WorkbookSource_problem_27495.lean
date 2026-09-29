-- Prove2me | Theorems.Thm_WorkbookSource_problem_27495
-- name    : WorkbookSource.problem_27495
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:38.184036+00:00
-- url     : https://prove2.me/theorems/3d72988c-eea1-4990-a9f4-0fc3bd1e16d4
-- title:
--   A functional equation with constant displacement
-- statement:
--   In $f(x)-x=f(y)-y$ , true for any $x,y\in\mathbb R$ , just choose $y=0$ and you get $f(x)-x=f(0)-0$ and so $f(x)=x+f(0)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27495` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27495; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_27495 (f : ℝ → ℝ) (h : ∀ x y, f x - x = f y - y) : ∀ x, f x = x + f 0  :=  by sorry
