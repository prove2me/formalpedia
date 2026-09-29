-- Prove2me | Theorems.Thm_lean_workbook_plus_26112
-- name    : lean_workbook_plus_26112
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/08b29fc5-54a1-45c7-9f25-9349f6dcec86
-- statement:
--   Prove that for $m \in \mathbb{N}$, $1.\cos{\frac{\pi}{2m+1}}\cos{\frac{2\pi}{2m+1}}...\cos{\frac{m\pi}{2m+1}}=\frac{1}{2^m}$ and $2.\cos{\frac{\pi}{2m}}\cos{\frac{2\pi}{2m}}...\cos{\frac{(m-1)\pi}{2m}}=\frac{\sqrt{m}}{2^{m-1}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26112 : ∀ m : ℕ, (∏ k in Finset.range m, Real.cos (k * π / (2 * m + 1))) = 1 / 2 ^ m ∧ (∏ k in Finset.range (m - 1), Real.cos (k * π / (2 * m))) = (Real.sqrt m) / 2 ^ (m - 1)   :=  by sorry
