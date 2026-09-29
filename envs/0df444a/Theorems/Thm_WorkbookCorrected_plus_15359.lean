-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_15359
-- name    : WorkbookCorrected.plus_15359
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:21:24.708585+00:00
-- url     : https://prove2.me/theorems/0111e786-2b34-4047-89b5-524862494c3b
-- title:
--   A strict partial-sum bound for a rational multiplier recurrence
-- statement:
--   Let $\{a_n \}_{n=1}^{\infty}$ be a sequence such that $a_1=\frac 12$ and $a_n=\biggl( \frac{2n-3}{2n} \biggr) a_{n-1} \qquad \forall n \geq 2.$ Prove that for every positive integer $n,$ we have $\sum_{k=1}^n a_k <1.$
--
--   Formalization Note: The source starts at a1=1/2 and has a_n=(2n−3)/(2n)a_(n−1) for n≥2. This correction uses the equivalent forward recurrence a_(n+1)=(2n−1)/(2(n+1))a_n for n≥1, real arithmetic, and sums terms1 throughn. The original formalization shifted the initial value and sum without shifting the coefficient correctly.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_15359 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_15359; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_15359 (a : ℕ → ℝ) (h0 : a 1=1/2)
    (h : ∀ n : ℕ, 1≤n → a (n+1)=(2*(n:ℝ)-1)/(2*((n:ℝ)+1))*a n) :
    ∀ n : ℕ, 1≤n → ∑ k ∈ Finset.range n, a (k+1) < 1 := by sorry
