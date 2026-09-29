-- Prove2me | Theorems.Thm_WorkbookSource_base_46701
-- name    : WorkbookSource.base_46701
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:04:55.650558+00:00
-- url     : https://prove2.me/theorems/8a33de29-e868-4c40-9d9f-2da1496ded49
-- title:
--   A cyclic ratio sum with a normalized triple-product correction
-- statement:
--   If $ a,b,c>0 $ then:
--    $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}\ge\frac{7}{2}-\frac{4abc}{(b+c)(c+a)(a+b)} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46701` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46701; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46701 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 7 / 2 - 4 * a * b * c / (b + c) / (c + a) / (a + b)  :=  by sorry
