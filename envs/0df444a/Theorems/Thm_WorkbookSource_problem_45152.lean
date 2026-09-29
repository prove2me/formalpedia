-- Prove2me | Theorems.Thm_WorkbookSource_problem_45152
-- name    : WorkbookSource.problem_45152
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:54.074579+00:00
-- url     : https://prove2.me/theorems/2ec910b7-62d9-449d-b34d-0661b0778027
-- title:
--   Adding three reciprocal relations
-- statement:
--   Put $a=xyz-{1\over xyz}$ . Then $x-{1\over y}={a\over 6}, y-{1\over z}={a\over 3}, z-{1\over x}={a\over 2}$ . Summing up those three we get $x+y+z-{1\over x}-{1\over y}-{1\over z}=a$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_45152; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45152; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_45152  (x y z : ℝ)
  (a : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : a = x * y * z - 1 / (x * y * z))
  (h₂ : x - 1/y = a/6)
  (h₃ : y - 1/z = a/3)
  (h₄ : z - 1/x = a/2) :
  x + y + z - 1/x - 1/y - 1/z = a  :=  by sorry
