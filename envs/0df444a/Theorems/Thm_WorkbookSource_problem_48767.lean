-- Prove2me | Theorems.Thm_WorkbookSource_problem_48767
-- name    : WorkbookSource.problem_48767
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:35.411736+00:00
-- url     : https://prove2.me/theorems/3b768128-66ff-4576-8914-cb9d427468f4
-- title:
--   A fourth degree polynomial identity
-- statement:
--   Prove the identity $ a^4 + b^4 + c^4 - a^3 b - b^3 c - c^3 a = (a^2 + b^2 + ab) (a - b)^2 + (b^2 + bc + c^2)(a - c)(b - c) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48767` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48767; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_48767 : ∀ a b c : ℝ, a^4 + b^4 + c^4 - a^3 * b - b^3 * c - c^3 * a = (a^2 + b^2 + a * b) * (a - b)^2 + (b^2 + b * c + c^2) * (a - c) * (b - c)  :=  by sorry
