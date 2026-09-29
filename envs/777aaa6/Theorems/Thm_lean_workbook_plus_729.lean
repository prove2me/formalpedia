-- Prove2me | Theorems.Thm_lean_workbook_plus_729
-- name    : lean_workbook_plus_729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b07510b6-9425-4ba6-a3ed-ef734451d125
-- statement:
--   Solution: \n The induction step is: \n $2\sqrt{n}+\frac{1}{\sqrt{n+1}}\leq2\sqrt{n+1}$ $\Leftrightarrow2\sqrt{n^{2}+n}+1\leq2n+2$ $\Leftrightarrow2\sqrt{n^{2}+n}\leq2n+1$ $\Leftrightarrow4n^{2}+4n\leq4n^{2}+4n+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_729  (n : ℕ) :
  2 * Real.sqrt n + 1 / Real.sqrt (n + 1) ≤ 2 * Real.sqrt (n + 1)   :=  by sorry
