-- Prove2me | Theorems.Thm_lean_workbook_plus_33315
-- name    : lean_workbook_plus_33315
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/15370a1c-9d8c-4fb8-971a-3b1ba5568c81
-- statement:
--   Suppose $ x = \frac {k}{m}$ , $ (k, m) = 1$ . Then $ x^{n}+a_{n-1}x^{n-1}+a_{n-2}x^{n-2}+\ldots+a_{0}= 0$ becomes $ k^{n}+mk^{n-1}a_{n-1} +m^2k^{n-2}a_{n-2}+\ldots+m^{n-1}ka_1 + m^na_{0}= 0$ . Where do we go from here?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33315 (x : ℚ) (n : ℕ) (k : ℤ) (m : ℤ) (hx : x = k / m) (hkm : (k, m) = 1) : ∃ a : ℕ → ℤ, x^n + ∑ i in Finset.range n, a i * x^i = 0 ↔ k^n + ∑ i in Finset.range n, m^i * k^(n - i) * a i = 0   :=  by sorry
