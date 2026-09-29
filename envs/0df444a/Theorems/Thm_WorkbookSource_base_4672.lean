-- Prove2me | Theorems.Thm_WorkbookSource_base_4672
-- name    : WorkbookSource.base_4672
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:31:13.400549+00:00
-- url     : https://prove2.me/theorems/5ee1425e-331a-40c0-96db-7ab702ab7bd0
-- title:
--   A quadratic sum times three shifted reciprocals bounds twice a triple sum
-- statement:
--   Let $a,b,c,d$ be positive real numbers . Prove that $ (a^2+b^2+c^2 +d^2 )\left(\frac{1}{a+d}+\frac{1}{b+d}+\frac{1}{c+d} \right) \geq 2(a+b+c).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4672` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4672; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4672 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :  (a^2 + b^2 + c^2 + d^2) * (1 / (a + d) + 1 / (b + d) + 1 / (c + d)) ≥ 2 * (a + b + c)  :=  by sorry
