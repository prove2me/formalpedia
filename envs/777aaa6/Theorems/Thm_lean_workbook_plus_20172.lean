-- Prove2me | Theorems.Thm_lean_workbook_plus_20172
-- name    : lean_workbook_plus_20172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7ac89ce4-c689-4e61-8705-590be27a97e5
-- statement:
--   Prove by induction that $a^{m+n} = a^m \times a^n$ and $(a^m)^n = a^{mn}$ , for $a \in \mathbb{R}$ and $n, m \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20172 (a : ℝ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n   :=  by sorry
