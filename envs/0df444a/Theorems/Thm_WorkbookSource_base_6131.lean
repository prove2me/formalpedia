-- Prove2me | Theorems.Thm_WorkbookSource_base_6131
-- name    : WorkbookSource.base_6131
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:54.199188+00:00
-- url     : https://prove2.me/theorems/6f81fa3d-9831-45fe-9e8f-71286a8fda42
-- title:
--   A cyclic mixed reciprocal lower bound at fixed sum three
-- statement:
--   Let $a,b,c>0$ such that $a+b+c=3$ . Prove that: $\sum \frac{ab+c}{a+b} \geq \frac{11}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6131` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6131; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6131 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a * b + c) / (a + b) + (b * c + a) / (b + c) + (c * a + b) / (c + a) ≥ 11 / 4  :=  by sorry
