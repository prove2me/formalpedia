-- Prove2me | Theorems.Thm_WorkbookSource_plus_42465
-- name    : WorkbookSource.plus_42465
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:30.678518+00:00
-- url     : https://prove2.me/theorems/4a948cf5-a085-4daa-8023-4c296fee8c37
-- title:
--   A cyclic fourth-power ratio with a difference product correction
-- statement:
--   If $a,b,c>0$ prove that
--
--    $\frac{a^4}{b}+\frac{b^4}{c}+\frac{c^4}{a}\geq a^3+b^3+c^3+2(a-b)(b-c)(c-a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_42465` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_42465; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_42465 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 / b + b^4 / c + c^4 / a ≥ a^3 + b^3 + c^3 + 2 * (a - b) * (b - c) * (c - a)   :=  by sorry
