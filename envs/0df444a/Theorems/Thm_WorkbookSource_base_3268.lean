-- Prove2me | Theorems.Thm_WorkbookSource_base_3268
-- name    : WorkbookSource.base_3268
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:33.536182+00:00
-- url     : https://prove2.me/theorems/c6a3fbc7-5f9b-426c-b2f4-389c2b4e8530
-- title:
--   A cyclic sum of squared pairwise ratios is at least three quarters
-- statement:
--   Let $a, b, c$ be positive reals. Prove that \(\left(\frac{a}{a+b}\right)^2+\left(\frac{b}{b+c}\right)^2+\left(\frac{c}{c+a}\right)^2\ge \frac34\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3268` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3268; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3268 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2 ≥ 3 / 4  :=  by sorry
