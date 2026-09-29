-- Prove2me | Theorems.Thm_WorkbookSource_plus_14687
-- name    : WorkbookSource.plus_14687
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:52.342679+00:00
-- url     : https://prove2.me/theorems/200eaa3c-7b02-4aac-a90c-f0943e97753a
-- title:
--   A cyclic quartic expression with a squared pairwise sum is nonnegative
-- statement:
--   Prove that: $a^4+b^4+c^4+11/2(ab+bc+ca)^2+3(ab^3+bc^3+ca^3)+4(a^3b+b^3c+c^3a) \ge 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_14687` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_14687; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_14687 (a b c : ℝ) : a^4 + b^4 + c^4 + (11/2)*(a * b + b * c + c * a)^2 + 3 * (a * b^3 + b * c^3 + c * a^3) + 4 * (a^3 * b + b^3 * c + c^3 * a) ≥ 0   :=  by sorry
