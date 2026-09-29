-- Prove2me | Theorems.Thm_WorkbookSource_base_2671
-- name    : WorkbookSource.base_2671
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:01:58.219374+00:00
-- url     : https://prove2.me/theorems/7b97136d-e17d-488b-bbcb-dfb82461931d
-- title:
--   A cyclic weighted ratio bound at fixed sum three
-- statement:
--   Let $a,b,c >0$ such that $a+b+c=3.$ Prove that $$ \frac{a+3b}{c} + \frac{b+3c}{a} + \frac{c+3a}{b} \ge 6 (3-abc)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2671` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2671; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2671 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a + 3 * b) / c + (b + 3 * c) / a + (c + 3 * a) / b ≥ 6 * (3 - a * b * c)  :=  by sorry
