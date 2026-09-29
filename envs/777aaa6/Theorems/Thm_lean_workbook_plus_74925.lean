-- Prove2me | Theorems.Thm_lean_workbook_plus_74925
-- name    : lean_workbook_plus_74925
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/991748b5-cbbd-40ec-a4b5-c38c8ccfe9ea
-- statement:
--   Given $\left ( \frac{p-r}{q-s}\right)=-1$, prove that $|p-r|=|q-s|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74925 (p q r s : ℝ) : ((p - r) / (q - s)) = -1 → |p - r| = |q - s|   :=  by sorry
