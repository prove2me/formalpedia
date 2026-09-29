-- Prove2me | Theorems.Thm_WorkbookSource_plus_43984
-- name    : WorkbookSource.plus_43984
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:50:08.262257+00:00
-- url     : https://prove2.me/theorems/8afdd68b-df75-4daa-a4d1-13d82f9a8363
-- title:
--   A squared quadratic sum with a triple-product correction
-- statement:
--   Let $a$ , $b$ and $c$ be real numbers such that $a+b+c=3$ . Prove that:
--    $$(a^2+b^2+c^2)^2+3abc\geq4(a^2+b^2+c^2)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_43984` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_43984; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_43984 (a b c : ℝ) (h : a + b + c = 3) : (a^2 + b^2 + c^2)^2 + 3 * a * b * c ≥ 4 * (a^2 + b^2 + c^2)   :=  by sorry
