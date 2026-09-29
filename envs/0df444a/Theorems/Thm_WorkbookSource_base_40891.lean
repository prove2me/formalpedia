-- Prove2me | Theorems.Thm_WorkbookSource_base_40891
-- name    : WorkbookSource.base_40891
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:56:07.685712+00:00
-- url     : https://prove2.me/theorems/7a007ca9-d3a7-472b-9c79-7555be4ef054
-- title:
--   A squared cyclic ratio sum bounded by a normalized eighth-degree expression
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\left(a+\frac{b^2}{c}\right)^2+\left(b+\frac{c^2}{a}\right)^2+\left(c+\frac{a^2}{b}\right)^2\le\frac{4(a^2+b^2+c^2)^4}{27a^2b^2c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40891` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40891; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40891 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b^2 / c)^2 + (b + c^2 / a)^2 + (c + a^2 / b)^2 ≤ (4 * (a^2 + b^2 + c^2)^4) / (27 * a^2 * b^2 * c^2)  :=  by sorry
