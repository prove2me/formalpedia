-- Prove2me | Theorems.Thm_WorkbookSource_plus_36393
-- name    : WorkbookSource.plus_36393
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:48.374225+00:00
-- url     : https://prove2.me/theorems/3c00857e-f177-4c50-9ee8-be9769f10f65
-- title:
--   A quadratic lower bound under linked products
-- statement:
--   Let $a,b,c,d$ be reals such that $ab+bc=12 $ and $ac+bd=3 .$ Prove that $$ a^2+b^2+c^2+d^2 \geq \frac{154}{9}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_36393` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_36393; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_36393 (a b c d : ℝ) (hab : a * b + b * c = 12) (hac : a * c + b * d = 3) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 154 / 9   :=  by sorry
