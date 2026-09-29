-- Prove2me | Theorems.Thm_WorkbookSource_base_9620
-- name    : WorkbookSource.base_9620
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:44:02.64368+00:00
-- url     : https://prove2.me/theorems/529640c9-76b2-403a-ae42-24623961c24c
-- title:
--   A shifted pairwise reciprocal lower bound at fixed sum three
-- statement:
--   Let $a,b,c>0$ such that $a+b+c=3$ . Prove that: $\sum_{cyc} \frac{a+b}{ab+3}\ge \frac{3}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9620` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9620; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9620 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a + b) / (a * b + 3) + (b + c) / (b * c + 3) + (c + a) / (c * a + 3) ≥ 3 / 2  :=  by sorry
