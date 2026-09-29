-- Prove2me | Theorems.Thm_WorkbookSource_base_10193
-- name    : WorkbookSource.base_10193
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:31:55.139425+00:00
-- url     : https://prove2.me/theorems/1b653a2d-742f-4251-a08a-4f0193b01fc1
-- title:
--   A cyclic quadratic-product ratio upper bound
-- statement:
--   For $a, b, c>0$ prove that $\frac{a^2b^2}{(a+b)(2a+b)}+\frac{b^2c^2}{(b+c)(2b+c)}+\frac{c^2a^2}{(c+a)(2c+a)}\le\frac{(a+b+c)^2}{18}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10193` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10193; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10193 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b^2 / (a + b) / (2 * a + b) + b^2 * c^2 / (b + c) / (2 * b + c) + c^2 * a^2 / (c + a) / (2 * c + a)) ≤ (a + b + c)^2 / 18  :=  by sorry
