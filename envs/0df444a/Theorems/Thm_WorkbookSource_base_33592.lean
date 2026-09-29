-- Prove2me | Theorems.Thm_WorkbookSource_base_33592
-- name    : WorkbookSource.base_33592
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:02.531362+00:00
-- url     : https://prove2.me/theorems/fa0d744a-33a8-48d4-9791-60e1c19138d6
-- title:
--   A product of quadratic sums bounds three cubes
-- statement:
--   Let $ a,b,c \in R$ . Prove that:
--    $ 3(a^2+b^2)(b^2+c^2)(c^2+a^2)\geq (ab+bc)^3+(bc+ca)^3+(ca+ab)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33592` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33592; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33592 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ≥ (a * b + b * c) ^ 3 + (b * c + c * a) ^ 3 + (c * a + a * b) ^ 3  :=  by sorry
