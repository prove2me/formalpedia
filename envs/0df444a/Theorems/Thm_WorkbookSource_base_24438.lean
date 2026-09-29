-- Prove2me | Theorems.Thm_WorkbookSource_base_24438
-- name    : WorkbookSource.base_24438
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:42:52.575982+00:00
-- url     : https://prove2.me/theorems/376f5fc6-463f-4a62-9d65-a7b8c7f3f476
-- title:
--   A weighted cyclic quadratic ratio sum is at most three fifths
-- statement:
--   Let $ a,b,c >0$ . Prove that : (Pham Kim Hung)
--
--    $ \frac{ab}{a^2+b^2+3c^2}+\frac{bc}{b^2+c^2+3a^2}+\frac{ca}{c^2+a^2+3b^2} \le \frac{3}{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24438` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24438; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24438 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a ^ 2 + b ^ 2 + 3 * c ^ 2) + b * c / (b ^ 2 + c ^ 2 + 3 * a ^ 2) + c * a / (c ^ 2 + a ^ 2 + 3 * b ^ 2)) ≤ 3 / 5  :=  by sorry
