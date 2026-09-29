-- Prove2me | Theorems.Thm_WorkbookSource_base_8483
-- name    : WorkbookSource.base_8483
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:37:57.12617+00:00
-- url     : https://prove2.me/theorems/02a9b71c-70e6-4d63-9839-3d29cd379d7e
-- title:
--   A cyclic fourth-power reciprocal sum bounds a cubed total
-- statement:
--   Prove that for any a,b,c >0 we have $\frac{a^4}{b+c} + \frac{b^4}{a+c} + \frac{c^4}{a+b} \geq \frac{1}{18}. (a+b+c)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8483` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8483; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8483 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 / (b + c) + b^4 / (a + c) + c^4 / (a + b)) ≥ (1 / 18) * (a + b + c)^3  :=  by sorry
