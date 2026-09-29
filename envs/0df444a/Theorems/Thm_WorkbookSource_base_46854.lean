-- Prove2me | Theorems.Thm_WorkbookSource_base_46854
-- name    : WorkbookSource.base_46854
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:39:48.713786+00:00
-- url     : https://prove2.me/theorems/57a83d14-f2aa-4322-81b2-d04ad04bc124
-- title:
--   A bilinear upper bound under a quadratic constraint
-- statement:
--   Let $a$ and $b$ be real numbers such that $9a^2+8ab+7b^2\leq6$. Prove that $7a+5b+12ab\leq9$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46854` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46854; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46854 (a b : ℝ) (h : 9 * a ^ 2 + 8 * a * b + 7 * b ^ 2 ≤ 6) :
 7 * a + 5 * b + 12 * a * b ≤ 9  :=  by sorry
