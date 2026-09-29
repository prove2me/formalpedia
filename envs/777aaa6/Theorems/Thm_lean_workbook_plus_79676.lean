-- Prove2me | Theorems.Thm_lean_workbook_plus_79676
-- name    : lean_workbook_plus_79676
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3c88b6c7-92e6-4d49-ad5b-a2a1143a9207
-- statement:
--   Prove that $\frac{1}{4}+\frac{2}{4^2}+\frac{3}{4^3}+\cdots+\frac{n}{4^n}<\frac{1}{2}$ for each $n\in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79676 (n : ℕ) : (∑ k in Finset.range n, (k + 1) / (4 ^ (k + 1))) < 1 / 2   :=  by sorry
