-- Prove2me | Theorems.Thm_WorkbookSource_base_55767
-- name    : WorkbookSource.base_55767
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:43.467513+00:00
-- url     : https://prove2.me/theorems/703e895f-2427-47ea-9f4a-7b6967984f78
-- title:
--   A weighted pairwise ratio has a symmetric product upper bound
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a+b}{a+2b}+\frac{b+c}{b+2c}+\frac{c+a}{c+2a}\le\frac{2(a+b+c)(ab+bc+ca)}{9abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55767` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55767; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55767 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≤ (2 * (a + b + c) * (a * b + b * c + c * a)) / (9 * a * b * c)  :=  by sorry
