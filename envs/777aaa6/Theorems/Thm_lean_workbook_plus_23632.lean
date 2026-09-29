-- Prove2me | Theorems.Thm_lean_workbook_plus_23632
-- name    : lean_workbook_plus_23632
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/bc5fb68c-86ce-4ab9-95c1-e702ef70f264
-- statement:
--   $\cos 3x = \cos(2x+x) = \cos 2x\cos x-\sin 2x \sin x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23632 : ∀ x : ℝ, cos (3 * x) = cos (2 * x + x)   :=  by sorry
