-- Prove2me | Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve
-- name    : collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve
-- status  : Open
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:12:40.994425+00:00
-- url     : https://prove2.me/theorems/3c628eed-a5a7-46d4-b122-633ac4d29a8f
-- title:
--   Residual Collatz orbit mergers in the 15 modulo 16 branch after the bounded inverse search
-- statement:
--   Let $C$ denote the classical Collatz map and $m_{16}(y)$ the minimum value in its depth-16 inverse tree rooted at $y$. Let $n\ge2{,}310{,}000$ satisfy $n\equiv 15\pmod{16}$ and $n\bmod9\in\{0,1,3,6,7\}$. Retain the following exclusions from the earlier affine merger proof.
--
--   | Modulus | Excluded residues |
--   | --- | --- |
--   | 81 | 10 |
--   | 2304 | 1743, 1599 |
--   | 4608 | 2847, 735, 991, 2527, 3039, 4575 |
--
--   Assume every anchor through time $128$ passes the bound
--   $$
--   m_{16}(C^t(n))\ge n\quad \text{for all }0\le t\le128.
--   $$
--
--   Find a positive $k<n$ whose orbit meets the orbit of $n$:
--   $$
--   \exists k,a,b\in\mathbb N,\quad 0<k<n\quad\text{and}\quad C^a(n)=C^b(k).
--   $$
--
--   All indices count ordinary Collatz steps. The conclusion permits arbitrary finite indices. The new hypothesis includes the old forward-only prefix bound because each inverse tree includes its root.
-- source:
--   Open refinement of https://prove2.me/theorems/fb6534fa-21f1-4ec1-aa4f-1dfd40b70345. Adapted from the smaller-start and orbit-merger sieves in D. Bařina, Improved verification limit for the convergence of the Collatz conjecture (2025), Sections 3.2–3.3, https://link.springer.com/article/10.1007/s11227-025-07337-0. The unbounded conclusion here is open.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
