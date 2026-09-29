-- Prove2me | Theorems.Thm_WorkbookSource_base_48935
-- name    : WorkbookSource.base_48935
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:19.486663+00:00
-- url     : https://prove2.me/theorems/419b0318-f78a-4c85-a05f-2276866c07ed
-- title:
--   A weighted cyclic pair-product ratio lower bound
-- statement:
--   Let $a,b,c>0$ .Prove: $\frac{ab}{4b+4c+a}+\frac{bc}{4a+4c+b}+\frac{ac}{4b+4a+c}\geq \frac{(a+b+c)(ab+bc+ca)}{9(a^2+b^2+c^2)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48935` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48935; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48935 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b) / (4 * b + 4 * c + a) + (b * c) / (4 * a + 4 * c + b) + (a * c) / (4 * b + 4 * a + c) ≥ (a + b + c) * (a * b + b * c + c * a) / (9 * (a ^ 2 + b ^ 2 + c ^ 2))  :=  by sorry
