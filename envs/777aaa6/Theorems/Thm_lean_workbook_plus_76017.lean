-- Prove2me | Theorems.Thm_lean_workbook_plus_76017
-- name    : lean_workbook_plus_76017
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f0723e7f-cedf-436b-9c7b-9627d0984cd7
-- statement:
--   Prove that $\frac{1}{\sqrt{k}+\sqrt{k+1}} = \sqrt{k+1}-\sqrt{k}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76017 : ∀ k : ℝ, k > 0 → 1 / (Real.sqrt k + Real.sqrt (k + 1)) = Real.sqrt (k + 1) - Real.sqrt k   :=  by sorry
