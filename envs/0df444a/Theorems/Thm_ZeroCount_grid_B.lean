-- Prove2me | Theorems.Thm_ZeroCount_grid_B
-- name    : ZeroCount.grid_B
-- status  : Open
-- author  : @xuanji
-- created : 2026-11-24T04:01:17.483807+00:00
-- url     : https://prove2.me/theorems/7fdb0d7b-3bdd-4a4d-ab21-192a66520a63
-- title:
--   Critical-line zeros above t for the Schoenfeld low-height count (grid_B)
-- statement:
--   For every height $t$ in the stated range there is a finite set $s$ of real numbers $x$ with $t<x\le 65000$ and $\zeta(\tfrac12+ix)=0$ such that
--   $$85288-|s| \le \frac{t}{2\pi}\Big(\log\frac{t}{2\pi}-1\Big)+\frac52 ,$$
--   and (for the band lemmas) a set of the stated cardinality of such critical-line zeros above the lower endpoint. These are the numerical line-zero inputs to the Schoenfeld-type bound $N(t)\le \frac{t}{2\pi}(\log\frac{t}{2\pi}-1)+\frac52$ for $14\le t\le 2500$, since $N(65000)\le 85288$.
-- source:
--   Broughan RH collection, Schoenfeld zero-count lemma (zerocount lane)

import Mathlib

theorem ZeroCount.grid_B :
    (∀ t : ℝ, 121 ≤ t → t < 520 →
      ∃ s : Finset ℝ, (85288 : ℝ) - s.card ≤
          t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) + 5 / 2 ∧
        ∀ x ∈ s, t < x ∧ x ≤ 65000 ∧ riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0) ∧
    (∃ s : Finset ℝ, s.card = 85250 ∧
      ∀ x ∈ s, 121 < x ∧ x ≤ 65000 ∧
        riemannZeta (1 / 2 + (x : ℂ) * Complex.I) = 0) := by sorry
