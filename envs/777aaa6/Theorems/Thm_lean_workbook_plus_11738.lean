-- Prove2me | Theorems.Thm_lean_workbook_plus_11738
-- name    : lean_workbook_plus_11738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3f574dd6-43af-47bd-bb3f-7169a918fe67
-- statement:
--   so $27n = 22 \cdot 675 \implies n = \boxed{550}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11738  (n : ℕ)
  (h₀ : 27 * n = 22 * 675) :
  n = 550   :=  by sorry
