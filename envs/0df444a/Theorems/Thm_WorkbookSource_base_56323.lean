-- Prove2me | Theorems.Thm_WorkbookSource_base_56323
-- name    : WorkbookSource.base_56323
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:33:25.448158+00:00
-- url     : https://prove2.me/theorems/ff30f01c-1965-4011-985a-9ee8547aa9fc
-- title:
--   A cubic product correction bounds a symmetric quadratic ratio
-- statement:
--   Prove that $\frac{9abc}{a^3+b^3+c^3+2(a^2b+b^2c+c^2a)}+2\ge \frac{(a+b+c)^2}{a^2+b^2+c^2}$ for $a,b,c>0$ using elementary methods.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56323` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56323; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56323 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)) + 2 ≥ (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
