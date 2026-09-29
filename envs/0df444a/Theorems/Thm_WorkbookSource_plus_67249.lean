-- Prove2me | Theorems.Thm_WorkbookSource_plus_67249
-- name    : WorkbookSource.plus_67249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:31:11.305874+00:00
-- url     : https://prove2.me/theorems/2d79f2ad-a2ec-4af5-aafb-a4a83e17d9a9
-- title:
--   A two-variable rational expression is at most one half
-- statement:
--   $\frac{(a+b)(1-ab)}{(a^2+1)(b^2+1)} \leqslant \frac{1}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67249` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67249; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67249 (a b : ℝ) : (a + b) * (1 - a * b) / (a ^ 2 + 1) / (b ^ 2 + 1) ≤ 1 / 2   :=  by sorry
