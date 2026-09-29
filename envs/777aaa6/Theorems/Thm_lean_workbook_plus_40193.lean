-- Prove2me | Theorems.Thm_lean_workbook_plus_40193
-- name    : lean_workbook_plus_40193
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/812404e2-c8eb-48fe-b19b-265e89f985ae
-- statement:
--   If we select 2 different pairs to form a matrix , total matrices formed by row rearrangements = $ \dbinom{3}{2} \times 4! = 72 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40193 (Nat.choose 3 2 * Nat.factorial 4) = 72   :=  by sorry
