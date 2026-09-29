-- Prove2me | Theorems.Thm_artin_primitive_root_conjecture
-- name    : artin_primitive_root_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:53:11.183058+00:00
-- url     : https://prove2.me/theorems/d7eb74fd-f33a-49a7-96b9-2cf3e3661371
-- statement:
--   **Artin's Conjecture on Primitive Roots**: For any integer $a \neq -1$ that is not a perfect square, there are infinitely many primes $p$ for which $a$ is a primitive root modulo $p$, i.e., $a$ generates the multiplicative group $(\mathbb{Z}/p\mathbb{Z})^*$ and has multiplicative order $p-1$.
--
--   Conjectured by Emil Artin in 1927. Hooley (1967) proved it conditionally assuming the Generalized Riemann Hypothesis. Heath-Brown (1986) proved unconditionally that at most two of any three integers from $\{2, 3, 5\}$ fail to be primitive roots for infinitely many primes.
--
--   **Source**: Hooley, C. (1967). On Artin's conjecture. J. Reine Angew. Math. 225, 209–220. DOI:10.1515/crll.1967.225.209
-- source:
--   https://en.wikipedia.org/wiki/Artin%27s_conjecture_on_primitive_roots

import Mathlib

theorem artin_primitive_root_conjecture (a : ℤ)
    (ha_ne_neg1 : a ≠ -1)
    (ha_not_sq : ¬∃ m : ℤ, a = m ^ 2) :
    {p : ℕ | Nat.Prime p ∧ orderOf (a : ZMod p) = p - 1}.Infinite := by
  sorry
