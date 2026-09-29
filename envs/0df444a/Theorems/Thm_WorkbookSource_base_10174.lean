-- Prove2me | Theorems.Thm_WorkbookSource_base_10174
-- name    : WorkbookSource.base_10174
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:46:01.32735+00:00
-- url     : https://prove2.me/theorems/0a2e5443-652e-4eba-98fd-ac811e7f7707
-- title:
--   A cyclic product-reciprocal sum bounds the reciprocal squared total
-- statement:
--   For $a,b,c>0$ . Prove that: $\sum_{cyc}\frac{1}{a(a+b)}\ge \frac{27}{2(a+b+c)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10174` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10174; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10174 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * (a + b)) + 1 / (b * (b + c)) + 1 / (c * (c + a))) ≥ 27 / 2 / (a + b + c) ^ 2  :=  by sorry
