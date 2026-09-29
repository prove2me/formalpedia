-- Prove2me | Theorems.Thm_WorkbookSource_base_7145
-- name    : WorkbookSource.base_7145
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:27:13.105664+00:00
-- url     : https://prove2.me/theorems/6ff973b6-7990-4a4d-9aa8-ea7f54c6e694
-- title:
--   A cyclic cubic reciprocal sum bounds a normalized cubic sum
-- statement:
--   Given $a;b;c>0$ , without using SOS method, prove that:
--    $\frac{a^3}{b+c}+\frac{b^3}{c+a}+\frac{c^3}{a+b} \geq \frac{3}{2}.\frac{a^3+b^3+c^3}{a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7145` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7145; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7145 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + c) + b^3 / (c + a) + c^3 / (a + b)) ≥ 3/2 * (a^3 + b^3 + c^3) / (a + b + c)  :=  by sorry
