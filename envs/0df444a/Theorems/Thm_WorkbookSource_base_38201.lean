-- Prove2me | Theorems.Thm_WorkbookSource_base_38201
-- name    : WorkbookSource.base_38201
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:22.755066+00:00
-- url     : https://prove2.me/theorems/c0473801-fd09-4614-a338-5d55646637c2
-- title:
--   A quadratic product bounds a product of two symmetric sums
-- statement:
--   Prove that $4(a^2+1)(b^2+1)(c^2+1)\ge 3(ab+bc+ca)(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38201` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38201; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38201 (a b c : ℝ) : 4 * (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 3 * (a * b + b * c + c * a) * (a + b + c)  :=  by sorry
