-- Prove2me | Theorems.Thm_WorkbookSource_problem_18562
-- name    : WorkbookSource.problem_18562
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:37:02.240703+00:00
-- url     : https://prove2.me/theorems/6537b3f3-2a07-47c5-b9ea-75b21fbdde26
-- title:
--   A repunit is divisible by499
-- statement:
--   1996 factors into $4\cdot 499$ . By Fermat's Little Theorem, $10^{498}\equiv 1\pmod{499}\Rightarrow \frac{10^{498}-1}{9}=\underbrace{11111\cdots }_{498}$ is divisible by 499.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18562` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18562; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_18562 :
  499 ∣ (10^498 - 1)/9  :=  by sorry
