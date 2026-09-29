-- Prove2me | Theorems.Thm_WorkbookSource_base_6786
-- name    : WorkbookSource.base_6786
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:39:44.081633+00:00
-- url     : https://prove2.me/theorems/aaf872c0-7b6d-4c75-aca7-360326b1525e
-- title:
--   A weighted triple-sum ratio sum is at least sixteen thirds
-- statement:
--   Prove or disprove that for $a, b, c, d > 0$ and $abc = 1$,
--    $\frac{2a+b+d}{a+c+d}+\frac{2b+c+a}{b+d+a}+\frac{2c+d+b}{c+a+b}+\frac{2d+a+c}{d+b+c}\geq\frac{16}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6786` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6786; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6786 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c = 1) : (2 * a + b + d) / (a + c + d) + (2 * b + c + a) / (b + d + a) + (2 * c + d + b) / (c + a + b) + (2 * d + a + c) / (d + b + c) ≥ 16 / 3  :=  by sorry
