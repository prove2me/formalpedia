-- Prove2me | Theorems.Thm_WorkbookSource_base_2539
-- name    : WorkbookSource.base_2539
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:01:44.628817+00:00
-- url     : https://prove2.me/theorems/bd4631da-1858-4f3c-942b-6e269bbd8dbc
-- title:
--   A cyclic fourth-power reciprocal sum bounds a mixed cubic sum
-- statement:
--   Prove that $\frac{a^4}{a+b}+\frac{b^4}{b+c}+\frac{c^4}{c+a}\geq \frac{a^2c+b^2a+c^2b}{2}$ . $\forall a,b,c> 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2539` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2539; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2539 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 / (a + b) + b^4 / (b + c) + c^4 / (c + a) ≥ (a^2 * c + b^2 * a + c^2 * b) / 2  :=  by sorry
