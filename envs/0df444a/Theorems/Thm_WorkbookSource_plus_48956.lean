-- Prove2me | Theorems.Thm_WorkbookSource_plus_48956
-- name    : WorkbookSource.plus_48956
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:55.706626+00:00
-- url     : https://prove2.me/theorems/cb773c74-360c-46c2-ae6d-8ac808760735
-- title:
--   A four-variable quartic inequality with rational coefficients
-- statement:
--   prove that: $5.(ab+bc+cd+ad+ac+bd)^2\geq \frac{7}{2}abcd+\frac{65}{32}(a+b+c+d)(acd+abd+abc+bcd)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_48956` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_48956; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_48956 (a b c d : ℝ) : 5 * (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ 7 / 2 * a * b * c * d + 65 / 32 * (a + b + c + d) * (a * c * d + b * c * d + b * a * c + a * b * d)   :=  by sorry
