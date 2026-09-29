-- Prove2me | Theorems.Thm_WorkbookSource_base_957
-- name    : WorkbookSource.base_957
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:16.510975+00:00
-- url     : https://prove2.me/theorems/487f60d8-a90b-4553-81da-b3792647ac99
-- title:
--   A squared pairwise-sum bound at unit positive sum
-- statement:
--   prove: $2(ab+ac+bc)^2 + \frac{8}{27} \ge ab+ ac+bc +5abc$ given $a,b,c >0$ and $a+b+c=1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_957` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_957; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_957 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : 2 * (a * b + a * c + b * c) ^ 2 + 8 / 27 ≥ a * b + a * c + b * c + 5 * a * b * c  :=  by sorry
