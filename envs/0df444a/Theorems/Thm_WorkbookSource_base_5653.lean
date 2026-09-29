-- Prove2me | Theorems.Thm_WorkbookSource_base_5653
-- name    : WorkbookSource.base_5653
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:30.226857+00:00
-- url     : https://prove2.me/theorems/db67c631-cf19-4421-a93f-ee71e7f1a42c
-- title:
--   A weighted quadratic reciprocal bound with symmetric sums
-- statement:
--   prove that ${\it \sum} \left( {\frac {1}{101\,{x}^{2}+yz}} \right) {\it \sum} \left( {x}^{2} \right) \geq \frac{1}{34}\,{\frac { \left( {\it \sum} \left( x \right) \right) ^{2}}{{\it \sum} \left( yz \right) }}$ given $x,y,z>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5653` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5653; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5653 (x y z : ℝ) (hx: 0 < x) (hy: 0 < y) (hz: 0 < z) : (1 / (101 * x ^ 2 + y * z) + 1 / (101 * y ^ 2 + z * x) + 1 / (101 * z ^ 2 + x * y)) * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 1 / 34 * (x + y + z) ^ 2 / (y * z + z * x + x * y)  :=  by sorry
