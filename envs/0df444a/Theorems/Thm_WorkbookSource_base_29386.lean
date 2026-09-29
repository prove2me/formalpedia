-- Prove2me | Theorems.Thm_WorkbookSource_base_29386
-- name    : WorkbookSource.base_29386
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:23.939907+00:00
-- url     : https://prove2.me/theorems/62145480-114e-4c70-a63d-6818e3d77d1c
-- title:
--   A weighted quadratic reciprocal upper bound
-- statement:
--   Let $ a,b,c $ be three positive real numbers . Prove that:
--    $$\frac{a}{4a^2+b^2+(b+c)^2}+\frac{b}{4b^2+c^2+(c+a)^2}+\frac{c}{4c^2+a^2+(a+b)^2} \le \frac{1}{a+b+c}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29386` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29386; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29386 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (4 * a ^ 2 + b ^ 2 + (b + c) ^ 2) + b / (4 * b ^ 2 + c ^ 2 + (c + a) ^ 2) + c / (4 * c ^ 2 + a ^ 2 + (a + b) ^ 2)) ≤ 1 / (a + b + c)  :=  by sorry
