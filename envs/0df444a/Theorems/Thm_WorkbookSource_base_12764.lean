-- Prove2me | Theorems.Thm_WorkbookSource_base_12764
-- name    : WorkbookSource.base_12764
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:22:38.112982+00:00
-- url     : https://prove2.me/theorems/ccca37ef-baf8-4de4-9d64-3c083098e438
-- title:
--   A cyclic triple-product ratio sum is at most one twelfth of the squared total
-- statement:
--   Let $a, b, c, d>0$ . Prove that
--    $\frac{abc}{b+c+d}+\frac{bcd}{c+d+a}+\frac{cda}{d+a+b}+\frac{dab}{a+b+c}\le\frac{(a+b+c+d)^2}{12}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12764` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12764; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12764 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * b * c / (b + c + d) + b * c * d / (c + d + a) + c * d * a / (d + a + b) + d * a * b / (a + b + c)) ≤ (a + b + c + d) ^ 2 / 12  :=  by sorry
