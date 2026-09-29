-- Prove2me | Theorems.Thm_lean_workbook_plus_14453
-- name    : lean_workbook_plus_14453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0e4b3a39-b70c-4623-82b9-dd50d834d8f5
-- statement:
--   Let $m, n, x, y \in \mathbb{R^{+}}$. If $x + y = m + n$ and $xy = mn$, prove that $x = m$ or $x = n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14453 (x y m n : ℝ) (hx : 0 < x) (hy : 0 < y) (hm : 0 < m) (hn : 0 < n) (hxy : x + y = m + n) (hmn : x*y = m*n) : x = m ∨ x = n   :=  by sorry
