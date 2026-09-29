-- Prove2me | Theorems.Thm_lean_workbook_plus_20386
-- name    : lean_workbook_plus_20386
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/3bea3ecd-7170-4ea2-95d8-5b0aff674e98
-- statement:
--   Find the value of $ \lfloor\frac{1}{3}\sum_{k=1}^{2007}\frac{1}{\sqrt{k}}\rfloor$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20386 : ∃ k, ⌊(1/3)*∑ i in Finset.Icc (1 : ℕ) 2007, (1/Real.sqrt i)⌋ = k   :=  by sorry
