-- Prove2me | Theorems.Thm_collatz_coalescence_residual_seven_mod_thirtytwo_after_affine_sieve
-- name    : collatz_coalescence_residual_seven_mod_thirtytwo_after_affine_sieve
-- status  : Open
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:01:44.097905+00:00
-- url     : https://prove2.me/theorems/e473ae8c-7fa5-469a-9dd6-4c4fea27c393
-- title:
--   Residual Collatz orbit mergers in the 7 modulo 32 branch after the affine sieve
-- statement:
--   Let $C$ be the classical Collatz map. Let $n\ge2{,}310{,}000$ satisfy $n\equiv 7\pmod{32}$, with residue in $\{0,1,3,6,7\}$ modulo $9$. Assume $C^t(n)\ge n$ for every $0\le t\le128$. Exclude the following residues.
--
--   | Modulus | Excluded residues |
--   | --- | --- |
--   | 81 | 10 |
--   | 4608 | 4071 |
--   | 9216 | 7783 |
--
--   Find a smaller positive start whose orbit meets the orbit of $n$:
--
--   $$
--   \exists k,a,b\in\mathbb N,\quad 0<k<n\quad\text{and}\quad C^a(n)=C^b(k).
--   $$
--
--   This is the open portion of the branch after the certified orbit mergers are removed. The index bounds in the hypotheses concern ordinary Collatz steps. The conclusion permits arbitrary finite indices.
-- source:
--   Open refinement of https://prove2.me/theorems/dcea1320-5deb-41cf-b914-7861cd961321. David Bařina, Improved verification limit for the convergence of the Collatz conjecture (2025), Sections 3.2–3.3 and equation (6), https://link.springer.com/article/10.1007/s11227-025-07337-0. The explicit progressions are worked out for the Prove2Me global descent decomposition using the classical Collatz map. The paper describes finite verification sieves. This residual assertion is unbounded.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_coalescence_residual_seven_mod_thirtytwo_after_affine_sieve (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 7)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n)
    (h81 : n % 81 ≠ 10)
    (h4608 : n % 4608 ≠ 4071)
    (h9216 : n % 9216 ≠ 7783) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
