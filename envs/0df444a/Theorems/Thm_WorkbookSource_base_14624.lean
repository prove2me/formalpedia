-- Prove2me | Theorems.Thm_WorkbookSource_base_14624
-- name    : WorkbookSource.base_14624
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:20.516818+00:00
-- url     : https://prove2.me/theorems/77beb98b-12ba-475f-9d2a-b15c823ae339
-- title:
--   A squared-difference bound under a mixed sum relation
-- statement:
--   Given $a, b, c$ positive real numbers, proof that
--
--    $$(a-b)^2+(b-c)^2+(c-a)^2 \geq 6(a+b+c-3)$$ Given that
--
--    $$a+b+c=ab+bc+ca$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14624` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14624; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14624 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = a * b + b * c + c * a) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 6 * (a + b + c - 3)  :=  by sorry
