-- Prove2me | Theorems.Thm_WorkbookSource_problem_21444
-- name    : WorkbookSource.problem_21444
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:34.193927+00:00
-- url     : https://prove2.me/theorems/7eb335a9-f8f9-46e4-97f8-352bb041f299
-- title:
--   An inequality for three ordered numbers
-- statement:
--   For real $0<x<y<z<1$, prove $$x^2+y^2+z^2<xy+xz+yz+z-x.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21444` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21444; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_21444  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x < y)
  (h₂ : y < z)
  (h₃ : z < 1) :
  x^2 + y^2 + z^2 < x * y + x * z + y * z + z - x  :=  by sorry
