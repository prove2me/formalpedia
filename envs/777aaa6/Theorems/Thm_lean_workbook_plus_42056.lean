-- Prove2me | Theorems.Thm_lean_workbook_plus_42056
-- name    : lean_workbook_plus_42056
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2277f865-4ac2-42ad-84e1-5f6281a4c663
-- statement:
--   When $a\ge b \, then sina\ge sinb\, a,b\in(0;\pi/2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42056 (a b: ℝ) (ha : 0 < a ∧ a < π / 2) (hb : 0 < b ∧ b < π / 2): a ≥ b → sin a ≥ sin b   :=  by sorry
