-- Prove2me | Theorems.Thm_collatz_coalescence_residual_seven_mod_thirtytwo_after_preimage_sieve
-- name    : collatz_coalescence_residual_seven_mod_thirtytwo_after_preimage_sieve
-- status  : Open
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:12:40.165707+00:00
-- url     : https://prove2.me/theorems/361a5d1d-53e8-4c4b-a89a-5aa7fd33614c
-- title:
--   Residual Collatz orbit mergers in the 7 modulo 32 branch after the bounded inverse search
-- statement:
--   Let $C$ denote the classical Collatz map and $m_{16}(y)$ the minimum value in its depth-16 inverse tree rooted at $y$. Let $n\ge2{,}310{,}000$ satisfy $n\equiv 7\pmod{32}$ and $n\bmod9\in\{0,1,3,6,7\}$. Retain the following exclusions from the earlier affine merger proof.
--
--   | Modulus | Excluded residues |
--   | --- | --- |
--   | 81 | 10 |
--   | 4608 | 4071 |
--   | 9216 | 7783 |
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
--   Open refinement of https://prove2.me/theorems/e473ae8c-7fa5-469a-9dd6-4c4fea27c393. Adapted from the smaller-start and orbit-merger sieves in D. Bařina, Improved verification limit for the convergence of the Collatz conjecture (2025), Sections 3.2–3.3, https://link.springer.com/article/10.1007/s11227-025-07337-0. The unbounded conclusion here is open.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_seven_mod_thirtytwo_after_preimage_sieve (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 7)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h4608 : n % 4608 ≠ 4071)
    (h9216 : n % 9216 ≠ 7783) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
