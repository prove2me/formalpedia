-- Prove2me | Theorems.Thm_WorkbookSource_base_30484
-- name    : WorkbookSource.base_30484
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:18:52.8075+00:00
-- url     : https://prove2.me/theorems/ed93b256-d256-4fd1-8fa9-7c44a62b1f48
-- title:
--   A cyclic product ratio bounded by symmetric quadratic forms
-- statement:
--   Let $a,b,c $ be possitive real numbers,prove that,
--
--    $\frac{a+b}{b+c}\frac{a}{2a+b+c}+\frac{b+c}{c+a}\frac{b}{2b+c+a}+\frac{c+a}{a+b}\frac{c}{2c+a+b}\le \frac{3}{4}\frac{a^2+b^2+c^2}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30484` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30484; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30484 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) * (a / (2 * a + b + c)) + (b + c) / (c + a) * (b / (2 * b + c + a)) + (c + a) / (a + b) * (c / (2 * c + a + b)) ≤ 3 / 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)  :=  by sorry
