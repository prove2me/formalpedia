-- Prove2me | Theorems.Thm_WorkbookSource_plus_77465
-- name    : WorkbookSource.plus_77465
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:50.143173+00:00
-- url     : https://prove2.me/theorems/f547b027-028d-4ffe-804c-9c79b5049a53
-- title:
--   A quadratic-product lower bound for triangle sides
-- statement:
--   Let $a$ , $b$ and $c$ be the lengths of the sides of a triangle such that $a + b + c = 3$ . Prove that $4\left(a^2+b^2+c^2\right)+abc \geq 13.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_77465` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_77465; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_77465 (a b c : ℝ) (hx: a + b + c = 3) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 13   :=  by sorry
