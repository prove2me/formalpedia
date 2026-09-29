-- Prove2me | Theorems.Thm_WorkbookSource_base_47517
-- name    : WorkbookSource.base_47517
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:05:14.57831+00:00
-- url     : https://prove2.me/theorems/bb77d651-b3bb-45e4-89c6-ee41cb6eda8a
-- title:
--   A four-variable cubic difference ratio sum is nonnegative
-- statement:
--   4-var: Let $a,b,c,d>0$ ,prove that: ${\frac {{d}^{3}-abc}{a+b+c}}+{\frac {{a}^{3}-bcd}{b+c+d}}+{\frac {{b}^{3}-acd}{a+c+d}}+{\frac {{c}^{3}-abd}{d+a+b}}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47517` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47517; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47517 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (d^3 - a * b * c) / (a + b + c) + (a^3 - b * c * d) / (b + c + d) + (b^3 - a * c * d) / (a + c + d) + (c^3 - a * b * d) / (d + a + b) ≥ 0  :=  by sorry
