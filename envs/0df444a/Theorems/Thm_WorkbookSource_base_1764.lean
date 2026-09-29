-- Prove2me | Theorems.Thm_WorkbookSource_base_1764
-- name    : WorkbookSource.base_1764
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:34.014762+00:00
-- url     : https://prove2.me/theorems/9c2d69ad-c090-4bef-bd1a-7f377a7baeec
-- title:
--   A weighted four-variable cyclic linear ratio sum is at least eight
-- statement:
--   Let $a$ , $b$ , $c$ and $d$ be positive numbers. Prove that:
--    $$\frac{a+3b}{b+c}+\frac{b+3c}{c+d}+\frac{c+3d}{d+a}+\frac{d+3a}{a+b}\geq8.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1764` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1764; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1764 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + 3 * b) / (b + c) + (b + 3 * c) / (c + d) + (c + 3 * d) / (d + a) + (d + 3 * a) / (a + b) ≥ 8  :=  by sorry
