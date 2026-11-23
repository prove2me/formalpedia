-- Prove2me | Theorems.Thm_collatz_coalescence_affine_progressions
-- name    : collatz_coalescence_affine_progressions
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:01:45.256516+00:00
-- url     : https://prove2.me/theorems/e39d4a9f-dfbd-4dbb-9ef7-5adc125ba037
-- title:
--   Collatz orbit mergers on twelve affine progressions
-- statement:
--   Let $C$ be the classical Collatz map. Suppose $n$ satisfies one of the residue conditions in the table.
--
--   | Modulus | Admitted residues |
--   | --- | --- |
--   | 81 | 10 |
--   | 4608 | 4071, 2847, 735, 991, 2527, 3039, 4575 |
--   | 9216 | 7783, 1563 |
--   | 2304 | 1743, 1599 |
--
--   Then the orbit of $n$ meets the orbit of a smaller positive start:
--
--   $$
--   \exists k,a,b\in\mathbb N,\quad 0<k<n\quad\text{and}\quad C^a(n)=C^b(k).
--   $$
--
--   The indices count ordinary Collatz steps. A common iterate can be above the starting value. These progressions can be discharged in a strong-induction proof of Collatz descent even when a bounded search for forward descent does not succeed.
-- source:
--   David Bařina, Improved verification limit for the convergence of the Collatz conjecture (2025), Sections 3.2–3.3 and equation (6), https://link.springer.com/article/10.1007/s11227-025-07337-0. The explicit progressions are worked out for the Prove2Me global descent decomposition using the classical Collatz map.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_affine_progressions (n : ℕ)
    (h : n % 81 = 10 ∨
      n % 4608 = 4071 ∨
      n % 9216 = 7783 ∨
      n % 9216 = 1563 ∨
      n % 2304 = 1743 ∨
      n % 2304 = 1599 ∨
      n % 4608 = 2847 ∨
      n % 4608 = 735 ∨
      n % 4608 = 991 ∨
      n % 4608 = 2527 ∨
      n % 4608 = 3039 ∨
      n % 4608 = 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
