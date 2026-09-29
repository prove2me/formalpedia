-- Prove2me | Theorems.Thm_WorkbookSource_problem_16562
-- name    : WorkbookSource.problem_16562
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:50.549985+00:00
-- url     : https://prove2.me/theorems/057f0c49-10e8-4917-bc33-6bab47002b09
-- title:
--   A sum of powers modulo2011
-- statement:
--   Apply Fermat's Little Theorem to each of the terms and prove that $(-5)^{2011}+3^{2011}+2^{2011}\equiv(-5+3+2)\pmod{2011}=0\pmod{2011}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16562` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16562; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16562 : (-5 : ℤ) ^ 2011 + 3 ^ 2011 + 2 ^ 2011 ≡ 0 [ZMOD 2011]  :=  by sorry
