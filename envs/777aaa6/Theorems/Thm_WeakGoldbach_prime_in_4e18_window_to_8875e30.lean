-- Prove2me | Theorems.Thm_WeakGoldbach_prime_in_4e18_window_to_8875e30
-- name    : WeakGoldbach.prime_in_4e18_window_to_8875e30
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T14:33:43.676989+00:00
-- url     : https://prove2.me/theorems/c51b7ad1-5e8b-46b7-8b97-5dbe5cc13322
-- title:
--   Prime gaps below $8.875\times 10^{30}$ are smaller than $4\cdot 10^{18}$
-- statement:
--   Put
--
--   $$
--   B = 4\cdot 10^{18}, \qquad T = 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000.
--   $$
--
--   For every natural number $x \le T - B$ there exists a prime $p$ with $x < p < x + B$. Equivalently, consecutive primes are less than $B$ apart throughout the range below $T$ — the covering property certified by the Helfgott–Platt computation.
-- source:
--   Helfgott–Platt, arXiv:1305.3062v2 §4

import Mathlib

namespace WeakGoldbach

theorem prime_in_4e18_window_to_8875e30 (x : ℕ)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  sorry

end WeakGoldbach
