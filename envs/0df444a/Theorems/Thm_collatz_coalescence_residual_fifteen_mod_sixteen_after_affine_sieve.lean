-- Prove2me | Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_affine_sieve
-- name    : collatz_coalescence_residual_fifteen_mod_sixteen_after_affine_sieve
-- status  : Open
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:01:45.355197+00:00
-- url     : https://prove2.me/theorems/fb6534fa-21f1-4ec1-aa4f-1dfd40b70345
-- title:
--   Residual Collatz orbit mergers in the 15 modulo 16 branch after the affine sieve
-- statement:
--   Let $C$ be the classical Collatz map. Let $n\ge2{,}310{,}000$ satisfy $n\equiv 15\pmod{16}$, with residue in $\{0,1,3,6,7\}$ modulo $9$. Assume $C^t(n)\ge n$ for every $0\le t\le128$. Exclude the following residues.
--
--   | Modulus | Excluded residues |
--   | --- | --- |
--   | 81 | 10 |
--   | 2304 | 1743, 1599 |
--   | 4608 | 2847, 735, 991, 2527, 3039, 4575 |
--
--   Find a smaller positive start whose orbit meets the orbit of $n$:
--
--   $$
--   \exists k,a,b\in\mathbb N,\quad 0<k<n\quad\text{and}\quad C^a(n)=C^b(k).
--   $$
--
--   This is the open portion of the branch after the certified orbit mergers are removed. The index bounds in the hypotheses concern ordinary Collatz steps. The conclusion permits arbitrary finite indices.
-- source:
--   Open refinement of https://prove2.me/theorems/ccdac836-6162-40c4-80f9-b1399d046d2a. David Bařina, Improved verification limit for the convergence of the Collatz conjecture (2025), Sections 3.2–3.3 and equation (6), https://link.springer.com/article/10.1007/s11227-025-07337-0. The explicit progressions are worked out for the Prove2Me global descent decomposition using the classical Collatz map. The paper describes finite verification sieves. This residual assertion is unbounded.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_fifteen_mod_sixteen_after_affine_sieve (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n)
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧ n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
