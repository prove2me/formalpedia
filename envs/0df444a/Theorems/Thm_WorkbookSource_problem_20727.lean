-- Prove2me | Theorems.Thm_WorkbookSource_problem_20727
-- name    : WorkbookSource.problem_20727
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:18.311131+00:00
-- url     : https://prove2.me/theorems/24947992-14fd-4d65-9486-23cc3442b7fa
-- title:
--   Rescaling a quadratic-cubic equation
-- statement:
--   If $x=2a, y=2b, z=2c,$ then $x^2+y^2+z^2=2xyz\implies (2a)^2+(2b)^2+(2c)^2=2.2a.2b.2c=16abc$ $\Rightarrow 4(a^2+b^2+c^2)=16abc.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20727` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20727; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_20727  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : x = 2 * a)
  (h₁ : y = 2 * b)
  (h₂ : z = 2 * c)
  (h₃ : x^2 + y^2 + z^2 = 2 * x * y * z) :
  4 * (a^2 + b^2 + c^2) = 16 * a * b * c  :=  by sorry
