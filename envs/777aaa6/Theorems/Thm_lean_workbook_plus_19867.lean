-- Prove2me | Theorems.Thm_lean_workbook_plus_19867
-- name    : lean_workbook_plus_19867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/edf046f6-6b39-40ee-a761-1c714232821d
-- statement:
--   $ y$ must be a multiple of $ 105$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19867 (y : ℕ) : y % 105 = 0 ↔ 105 ∣ y   :=  by sorry
