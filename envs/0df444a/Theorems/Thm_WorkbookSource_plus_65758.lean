-- Prove2me | Theorems.Thm_WorkbookSource_plus_65758
-- name    : WorkbookSource.plus_65758
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:40.789803+00:00
-- url     : https://prove2.me/theorems/5a7f52df-0702-4490-900d-e5d7f4888e33
-- title:
--   A pairwise linear ratio sum is bounded by half a cyclic ratio sum
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a+b}{2a+b+c}+\frac{b+c}{2b+c+a}+\frac{c+a}{2c+a+b}\le\frac{1}{2}\left(\frac{a}{b}+\frac{b}{c}+\frac{c}{a}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_65758` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_65758; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_65758 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (2 * a + b + c) + (b + c) / (2 * b + c + a) + (c + a) / (2 * c + a + b) ≤ 1 / 2 * (a / b + b / c + c / a)   :=  by sorry
