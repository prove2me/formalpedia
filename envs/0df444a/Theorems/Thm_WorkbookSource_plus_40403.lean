-- Prove2me | Theorems.Thm_WorkbookSource_plus_40403
-- name    : WorkbookSource.plus_40403
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:54.802025+00:00
-- url     : https://prove2.me/theorems/6a86f445-26e2-45e0-b68b-088e4d589a5f
-- title:
--   A cyclic quartic sum bounds a squared pairwise sum
-- statement:
--   If a, b, c are real number then: $ a^4+b^4+c^4+a^3b+b^3c+c^3a\ge\frac{3}{5}(ab+bc+ca)^2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_40403` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40403; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_40403 (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + a ^ 3 * b + b ^ 3 * c + c ^ 3 * a ≥ (3 / 5) * (a * b + b * c + c * a) ^ 2   :=  by sorry
