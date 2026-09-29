-- Prove2me | Theorems.Thm_lean_workbook_plus_35095
-- name    : lean_workbook_plus_35095
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/008f26c2-7d84-46d0-8f01-2eec881c7265
-- statement:
--   Let $r \in Q^+$ . Prove that if $\frac{r^2 + 1}{r} \leq 1$ , then $\frac{r^2 + 2}{r} \leq 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35095 (r : ℚ) (hr : 0 < r) : (r^2 + 1) / r ≤ 1 → (r^2 + 2) / r ≤ 2   :=  by sorry
