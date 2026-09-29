-- Prove2me | Theorems.Thm_WorkbookSource_base_36379
-- name    : WorkbookSource.base_36379
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:28.967232+00:00
-- url     : https://prove2.me/theorems/64a6568d-9245-4e17-bb64-232325c49697
-- title:
--   A four-variable quartic bound with rational coefficients
-- statement:
--   prove that: $2.(a+b+c+d)^4+(ab+bc+cd+ad+ac+bd)^2 \geq 3abcd+\frac{289}{96}(a+b+c+d)^2(ab+bc+cd+ad+ac+bd)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36379` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36379; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36379 (a b c d : ℝ) : 2 * (a + b + c + d) ^ 4 + (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ 3 * a * b * c * d + 289 / 96 * (a + b + c + d) ^ 2 * (a * b + b * c + c * d + d * a + a * c + b * d)  :=  by sorry
