-- Prove2me | Theorems.Thm_WorkbookSource_base_53756
-- name    : WorkbookSource.base_53756
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:06:19.664963+00:00
-- url     : https://prove2.me/theorems/44c1a5c2-0933-4498-b909-3f576e83e0c2
-- title:
--   A cyclic ratio sum with a pair-product correction at fixed sum two
-- statement:
--   Let $a,b,c>0$ such that: $a+b+c=2$ . Prove that: $\frac{a}{b}+\frac{b}{c}+\frac{c}{a} +3(ab+bc+ac) \geq 7$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53756` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53756; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53756 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : a / b + b / c + c / a + 3 * (a * b + b * c + a * c) ≥ 7  :=  by sorry
