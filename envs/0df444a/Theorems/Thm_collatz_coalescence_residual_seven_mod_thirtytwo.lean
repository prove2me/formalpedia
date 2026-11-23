-- Prove2me | Theorems.Thm_collatz_coalescence_residual_seven_mod_thirtytwo
-- name    : collatz_coalescence_residual_seven_mod_thirtytwo
-- status  : Open
-- author  : @Siyuan Chen
-- created : 2026-11-23T14:28:17.363565+00:00
-- url     : https://prove2.me/theorems/dcea1320-5deb-41cf-b914-7861cd961321
-- title:
--   Collatz orbits merging with smaller starts in the residual class 7 modulo 32
-- statement:
--   Let $C$ be the classical Collatz map. Suppose $n\ge 2{,}310{,}000$ is congruent to $7$ modulo $32$, its residue modulo $9$ belongs to $\{0,1,3,6,7\}$, and $C^t(n)\ge n$ for every $0\le t\le128$. Find a positive starting value $k<n$ whose Collatz orbit shares a point with the orbit of $n$:
--
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n\quad\text{and}\quad C^a(n)=C^b(k).
--   $$
--
--   The indices count ordinary Collatz steps. This branch is an open specialization of the orbit-merging criterion for the global descent principle. It allows a common point at or above $n$, so a certificate can use a smaller predecessor as well as a forward descent.
-- source:
--   Open specialization for the Prove2Me Collatz Conjecture mission, global descent milestone (https://prove2.me/theorems/574df5fa-afb5-46e8-b2c0-21635aee4a73). Its filters and common-orbit criterion are adapted from David Bařina, Improved verification limit for the convergence of the Collatz conjecture, J. Supercomputing (2025), Sections 3.2 and 3.3, https://doi.org/10.1007/s11227-025-07337-0. The paper describes the sieves for finite verification. The assertion here is an open, unbounded target.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_seven_mod_thirtytwo (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 7)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
