-- Prove2me | Theorems.Thm_WorkbookSource_base_13321
-- name    : WorkbookSource.base_13321
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:49:21.735654+00:00
-- url     : https://prove2.me/theorems/68acde02-ced1-4dd0-b6a1-d80d2776b11a
-- title:
--   A weighted quadratic cyclic ratio difference is nonnegative
-- statement:
--   Let a,b,c be positive real numbers. Prove that:
--    $ (a^{2}+2b^{2})(\frac{a}{c}-1)+(b^{2}+2c^{2})(\frac{b}{a}-1)+(c^{2}+2a^{2})(\frac{c}{b}-1)\ge 0$
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13321` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13321; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13321 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :  (a^2 + 2 * b^2) * (a / c - 1) + (b^2 + 2 * c^2) * (b / a - 1) + (c^2 + 2 * a^2) * (c / b - 1) ≥ 0  :=  by sorry
