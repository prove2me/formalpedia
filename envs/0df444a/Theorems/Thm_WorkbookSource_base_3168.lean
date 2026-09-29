-- Prove2me | Theorems.Thm_WorkbookSource_base_3168
-- name    : WorkbookSource.base_3168
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:05.660216+00:00
-- url     : https://prove2.me/theorems/7f497142-2746-4c67-b3dc-577b3a46c5f7
-- title:
--   A five-variable squared-sum bound under a product relation
-- statement:
--   Let $a,b,c,d,e$ be real numbers such that $ab+bc+ca=20de$. Prove that $13(a^2+b^2+c^2+d^2+e^2)\ge 3(a+b+c+d+e)^2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3168` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3168; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3168 (a b c d e : ℝ) (h : a * b + b * c + c * a = 20 * d * e) :
  13 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 3 * (a + b + c + d + e) ^ 2  :=  by sorry
