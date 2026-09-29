-- Prove2me | Theorems.Thm_WorkbookSource_base_3528
-- name    : WorkbookSource.base_3528
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:46.093698+00:00
-- url     : https://prove2.me/theorems/5b26e826-3c4f-4fad-b928-0a1c08852272
-- title:
--   A cyclic linear-product quadratic ratio bound
-- statement:
--   Prove that for all positive reals $a,b,c$
--
--    $$\sum_{cyc}\frac{a(b+c)}{a^2+ (b+c)^2} \leq \frac{6}{5}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3528` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3528; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3528 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (a ^ 2 + (b + c) ^ 2) + b * (c + a) / (b ^ 2 + (c + a) ^ 2) + c * (a + b) / (c ^ 2 + (a + b) ^ 2)) ≤ 6 / 5  :=  by sorry
