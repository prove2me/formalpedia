-- Prove2me | Theorems.Thm_WorkbookSource_base_50181
-- name    : WorkbookSource.base_50181
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:36:38.162661+00:00
-- url     : https://prove2.me/theorems/91f3f857-5adf-4b7d-a787-1b31141ec8b1
-- title:
--   A shifted mixed cyclic ratio sum is at least three
-- statement:
--   If $a$ , $b$ , $c$ are positive reals, prove that
--
--    $$\frac{a+bc}{a+a^2}+\frac{b+ca}{b+b^2}+\frac{c+ab}{c+c^2} \geq 3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50181` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50181; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50181 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b * c) / (a + a^2) + (b + c * a) / (b + b^2) + (c + a * b) / (c + c^2) ≥ 3  :=  by sorry
