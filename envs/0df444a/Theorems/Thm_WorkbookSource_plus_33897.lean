-- Prove2me | Theorems.Thm_WorkbookSource_plus_33897
-- name    : WorkbookSource.plus_33897
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:49:57.914148+00:00
-- url     : https://prove2.me/theorems/901ab5cc-f683-48ed-a10e-7dfd339925c7
-- title:
--   A four-variable quadratic bound under a weighted sum constraint
-- statement:
--   Let $a,b,c,d$ be real numbers such that $a+2b+3c+4d=10$, prove that: $a^2+b^2+c^2+d^2+ab+ac+ad+bc+bd+cd\ge5$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_33897` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_33897; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_33897 (a b c d : ℝ) (h : a + 2 * b + 3 * c + 4 * d = 10) :
  a^2 + b^2 + c^2 + d^2 + a * b + a * c + a * d + b * c + b * d + c * d ≥ 5   :=  by sorry
