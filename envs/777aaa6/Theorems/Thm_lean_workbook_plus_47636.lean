-- Prove2me | Theorems.Thm_lean_workbook_plus_47636
-- name    : lean_workbook_plus_47636
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/86bfcc30-3e96-4952-a9c1-eabe8059030a
-- statement:
--   [x] is meant as the biggest integer smaller than $ x$ . So $ [x]\leq x<[x]+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47636 (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1   :=  by sorry
