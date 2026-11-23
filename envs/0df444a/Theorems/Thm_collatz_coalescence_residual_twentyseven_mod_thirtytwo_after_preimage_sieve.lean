-- Prove2me | Theorems.Thm_collatz_coalescence_residual_twentyseven_mod_thirtytwo_after_preimage_sieve
-- name    : collatz_coalescence_residual_twentyseven_mod_thirtytwo_after_preimage_sieve
-- status  : Open
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:12:41.049033+00:00
-- url     : https://prove2.me/theorems/2f2c89a6-40b8-4b55-81e9-679859a06e43
-- title:
--   Residual Collatz orbit mergers in the 27 modulo 32 branch after the bounded inverse search
-- statement:
--   Let $C$ denote the classical Collatz map and $m_{16}(y)$ the minimum value in its depth-16 inverse tree rooted at $y$. Let $n\ge2{,}310{,}000$ satisfy $n\equiv 27\pmod{32}$ and $n\bmod9\in\{0,1,3,6,7\}$. Retain the following exclusions from the earlier affine merger proof.
--
--   | Modulus | Excluded residues |
--   | --- | --- |
--   | 81 | 10 |
--   | 9216 | 1563 |
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
--   Open refinement of https://prove2.me/theorems/5f29f9dd-c039-4529-86a6-6c9328679f43. Adapted from the smaller-start and orbit-merger sieves in D. Bařina, Improved verification limit for the convergence of the Collatz conjecture (2025), Sections 3.2–3.3, https://link.springer.com/article/10.1007/s11227-025-07337-0. The unbounded conclusion here is open.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_twentyseven_mod_thirtytwo_after_preimage_sieve (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 27)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h9216 : n % 9216 ≠ 1563) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
