-- Prove2me | Theorems.Thm_WorkbookSource_base_39714
-- name    : WorkbookSource.base_39714
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:52:03.598797+00:00
-- url     : https://prove2.me/theorems/2b3399c6-2b13-409a-9c72-aa82f8458430
-- title:
--   A symmetric quadratic inequality with a cubic reciprocal correction
-- statement:
--   Prove that $a^2+b^2+c^2+\frac{9abc(a^2+b^2+c^2)}{2(a^3+b^3+c^3)+3abc}\ge 2(ab+bc+ca)$ for $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39714` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39714; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39714 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 + (9 * a * b * c * (a^2 + b^2 + c^2)) / (2 * (a^3 + b^3 + c^3) + 3 * a * b * c) ≥ 2 * (a * b + b * c + a * c)  :=  by sorry
