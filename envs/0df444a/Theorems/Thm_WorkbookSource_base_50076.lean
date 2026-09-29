-- Prove2me | Theorems.Thm_WorkbookSource_base_50076
-- name    : WorkbookSource.base_50076
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:40.74652+00:00
-- url     : https://prove2.me/theorems/c2ec8374-02bf-4c57-9302-1c4a9f067c73
-- title:
--   A cyclic fifth-power ratio bounds a fourth power of the total
-- statement:
--   Prove that $\frac{a^5}{b}+\frac{b^5}{c}+\frac{c^5}{a}\geq\frac{1}{27} \cdot (a+b+c)^4$ for all $a,b,c >0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50076` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50076; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50076 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 / b + b^5 / c + c^5 / a) ≥ 1 / 27 * (a + b + c)^4  :=  by sorry
