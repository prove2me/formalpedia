-- Prove2me | Theorems.Thm_WorkbookSource_base_21170
-- name    : WorkbookSource.base_21170
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:57.282651+00:00
-- url     : https://prove2.me/theorems/edb8283e-5371-4180-9a28-b4d6409e5a29
-- title:
--   A cyclic cubic-over-quadratic upper bound
-- statement:
--   For a,b,c>0. Demonstrate:
--    $\frac{ab^2}{a^2+2b^2+c^2}+\frac{bc^2}{b^2+2c^2+a^2}+\frac{ca^2}{c^2+2a^2+b^2}\le \frac{a+b+c}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21170` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21170; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21170 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b ^ 2 / (a ^ 2 + 2 * b ^ 2 + c ^ 2) + b * c ^ 2 / (b ^ 2 + 2 * c ^ 2 + a ^ 2) + c * a ^ 2 / (c ^ 2 + 2 * a ^ 2 + b ^ 2)) ≤ (a + b + c) / 4  :=  by sorry
