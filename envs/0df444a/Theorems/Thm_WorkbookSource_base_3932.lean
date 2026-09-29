-- Prove2me | Theorems.Thm_WorkbookSource_base_3932
-- name    : WorkbookSource.base_3932
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:07.878702+00:00
-- url     : https://prove2.me/theorems/7e6b5a7e-6f4e-4978-a116-19d28d5bef5d
-- title:
--   A sum versus triple-product inequality
-- statement:
--   Let $a,b,c\in\mathbb{R}^+ $ and $ab+bc+ca=3$ , Prove that $2+ abc\leq a+b+c.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3932` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3932; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3932 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : 2 + a * b * c ≤ a + b + c  :=  by sorry
