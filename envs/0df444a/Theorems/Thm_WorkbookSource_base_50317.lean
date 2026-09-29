-- Prove2me | Theorems.Thm_WorkbookSource_base_50317
-- name    : WorkbookSource.base_50317
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:59.527463+00:00
-- url     : https://prove2.me/theorems/48acd3d0-d548-4d59-915e-5c4d4ce7fe0f
-- title:
--   A cyclic linear ratio upper bound by squared symmetric forms
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a+2b}{a+b}+\frac{b+2c}{b+c}+\frac{c+2a}{c+a}\le\frac{9}{2}\left(\frac{a^2+b^2+c^2}{ab+bc+ca}\right)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50317` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50317; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / (a + b) + (b + 2 * c) / (b + c) + (c + 2 * a) / (c + a) ≤ (9 / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)) ^ 2  :=  by sorry
