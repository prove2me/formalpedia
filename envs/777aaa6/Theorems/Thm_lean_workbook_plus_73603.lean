-- Prove2me | Theorems.Thm_lean_workbook_plus_73603
-- name    : lean_workbook_plus_73603
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/69c46027-a3e3-4632-ac15-f38b4da29890
-- statement:
--   Prove that $S\geq -1999.25$ where $S=\sum_{i=1}^{1999} a_{i}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73603 : ∀ a : ℕ → ℝ, (∑ i in Finset.range 1999, a i) ≥ -1999.25   :=  by sorry
