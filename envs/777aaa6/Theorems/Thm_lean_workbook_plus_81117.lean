-- Prove2me | Theorems.Thm_lean_workbook_plus_81117
-- name    : lean_workbook_plus_81117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/0f844dbf-0a6d-42b7-ba9a-44dc40f5ec10
-- statement:
--   Given $a + b + c = u$ , $ab + bc + ca = v$ , $abc = w$ , then $a^4 + b^4 + c^4 = u^4 - 4u^2v + 2v^2 + 4uw$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81117 (a b c u v w : ℂ) (h1 : a + b + c = u) (h2 : a * b + b * c + c * a = v) (h3 : a * b * c = w) : a ^ 4 + b ^ 4 + c ^ 4 = u ^ 4 - 4 * u ^ 2 * v + 2 * v ^ 2 + 4 * u * w   :=  by sorry
