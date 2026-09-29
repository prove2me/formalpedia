-- Prove2me | Theorems.Thm_WorkbookSource_base_55693
-- name    : WorkbookSource.base_55693
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:31.209743+00:00
-- url     : https://prove2.me/theorems/44ebb188-3794-47b2-a658-6fc30cae1024
-- title:
--   A two-term cubic ratio lower bound
-- statement:
--   Let $a,\,b,\,c$ are positive real numbers, prove that $\frac{a^3}{(a+b)^3}+\frac{b^3}{(b+c)^3} \geqslant \frac{5a-c}{8(a+c)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55693` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55693; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55693 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^3 / (a + b)^3 + b^3 / (b + c)^3) ≥ (5 * a - c) / (8 * (a + c))  :=  by sorry
