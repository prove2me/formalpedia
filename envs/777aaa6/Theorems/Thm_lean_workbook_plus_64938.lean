-- Prove2me | Theorems.Thm_lean_workbook_plus_64938
-- name    : lean_workbook_plus_64938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c663d3d4-5ce1-411c-ad6d-8f5baeb08ed4
-- statement:
--   Given $S = 2\cdot \frac{n(n+1)}{2}=n(n+1)$ and $T = \frac{n(n+1)}{2}$, prove that $\frac{S}{T} = 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64938 (n : ℕ) (hn : n ≠ 0) : 2 * (n * (n + 1) / 2) / (n * (n + 1) / 2) = 2   :=  by sorry
