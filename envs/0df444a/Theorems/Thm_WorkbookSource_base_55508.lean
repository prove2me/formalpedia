-- Prove2me | Theorems.Thm_WorkbookSource_base_55508
-- name    : WorkbookSource.base_55508
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:46.557326+00:00
-- url     : https://prove2.me/theorems/2fb9131c-bb6e-4736-99e1-8f4d029d5fe4
-- title:
--   A linear term and shifted square bound a harmonic product
-- statement:
--   Let $a,b$ be positive real numbers .Prove that
--
--    $$a+(b+1)^2\geq \frac{9ab}{a+b}$$ (Lijvzhi)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55508` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55508; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55508 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + (b + 1) ^ 2 ≥ 9 * a * b / (a + b)  :=  by sorry
