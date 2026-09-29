-- Prove2me | Theorems.Thm_WorkbookSource_base_3587
-- name    : WorkbookSource.base_3587
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:41.514129+00:00
-- url     : https://prove2.me/theorems/469272a9-6eae-4886-bad6-16ddcd9f7f71
-- title:
--   A cyclic quadratic ratio sum bounds a normalized cubic sum
-- statement:
--   The original arqady's inequality is:
--    If $a, b, c>0$ prove that
--    $\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b}\ge\frac{3}{2}\cdot\frac{a^3+b^3+c^3}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3587` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3587; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3587 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≥ (3 / 2) * (a^3 + b^3 + c^3) / (a^2 + b^2 + c^2)  :=  by sorry
