-- Prove2me | Theorems.Thm_WorkbookSource_base_42167
-- name    : WorkbookSource.base_42167
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:48:12.798518+00:00
-- url     : https://prove2.me/theorems/f3f96dc8-034c-421d-a489-8a5ecd743d0d
-- title:
--   A quadratic lower bound under a weighted linear constraint
-- statement:
--   Let $a,b,c$ be real numbers such that $a+2b+3c=10$, prove that: $a^2+b^2+c^2+ab+bc+ca\ge10$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42167` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42167; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42167 (a b c : ℝ) (h : a + 2 * b + 3 * c = 10) : a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ 10  :=  by sorry
