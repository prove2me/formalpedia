-- Prove2me | Theorems.Thm_collatz_coalescence_residual_twentyseven_mod_thirtytwo_without_odd_run_mergers
-- name    : collatz_coalescence_residual_twentyseven_mod_thirtytwo_without_odd_run_mergers
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T07:29:42.95341+00:00
-- url     : https://prove2.me/theorems/06067a9c-68bd-455a-bf8a-a7075404caff
-- title:
--   Residual mergers for 27 modulo 32 after the odd-run divisibility criterion
-- statement:
--   Let $C$ be the ordinary Collatz map and $M_{16}(y)$ the least natural number reaching $y$ in at most sixteen steps. Retain the [parent merger problem](https://prove2.me/theorems/2f2c89a6-40b8-4b55-81e9-679859a06e43)'s hypotheses: $n\ge2{,}310{,}000$, $n\equiv27\pmod{32}$, $n\bmod9\in\{0,1,3,6,7\}$, $n\not\equiv10\pmod{81}$, $n\not\equiv1563\pmod{9216}$, and $M_{16}(C^t(n))\ge n$ for $0\le t\le128$.
--
--   Suppose additionally that for every pair of nonnegative integers $a,m$ with $3\cdot2^{a+m}\le3^m$, the integer $2^a(3n+1)+1$ is not divisible by $3^m$. Show that $n$ shares an orbit point with a smaller positive start:
--   $$\exists k,u,v,\qquad 0<k<n,\quad C^u(n)=C^v(k).$$
-- source:
--   Residual case of https://prove2.me/theorems/2f2c89a6-40b8-4b55-81e9-679859a06e43 after applying collatz_smaller_merger_of_odd_run_divisibility.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_twentyseven_mod_thirtytwo_without_odd_run_mergers (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 27)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h9216 : n % 9216 ≠ 1563)
    (havoid : ∀ a m : ℕ, 3 * 2 ^ (a + m) ≤ 3 ^ m →
      ¬ 3 ^ m ∣ 2 ^ a * (3 * n + 1) + 1) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
