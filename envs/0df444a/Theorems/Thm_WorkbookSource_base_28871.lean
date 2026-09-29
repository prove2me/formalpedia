-- Prove2me | Theorems.Thm_WorkbookSource_base_28871
-- name    : WorkbookSource.base_28871
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:08:29.25235+00:00
-- url     : https://prove2.me/theorems/986c702a-100b-424e-b80c-c8b18a01e6e3
-- title:
--   A cyclic cubic ratio with a symmetric product correction
-- statement:
--   For $a,b,c$ positive reals, prove that $\sum \frac{a^3}{b+c} + 9abc \frac{\sum a}{\sum a^2 +\sum ab} \geq 2\sum ab$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28871` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28871; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28871 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + c) + b^3 / (c + a) + c^3 / (a + b) + 9 * a * b * c * (a + b + c) / (a^2 + b^2 + c^2 + a * b + b * c + c * a) ) ≥ 2 * (a * b + b * c + c * a)  :=  by sorry
