-- Prove2me | Theorems.Thm_lean_workbook_plus_29341
-- name    : lean_workbook_plus_29341
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/576b1508-4e49-420b-bbc9-fa06cec2b04d
-- statement:
--   If $P(x) \in \mathbb{Z}[x]$, then for every two distinct integers $a,b$ we have that $a-b | P(a) - P(b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29341 (P : Polynomial ℤ) {a b : ℤ} (h : a ≠ b) : a - b ∣ P.eval a - P.eval b   :=  by sorry
