-- Prove2me | Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
-- name    : WeakGoldbach.verified_three_odd_primes_to_8875e30
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T04:28:47.388455+00:00
-- url     : https://prove2.me/theorems/03eeb9c4-ae86-4918-80c4-bee21cefb6ac
-- title:
--   Verified all-odd ternary Goldbach range $[9,\, 8.875\times 10^{30}]$
-- statement:
--   For every odd natural number $n$ with
--
--   $$
--   9 \le n \le 8{,}875{,}694{,}145{,}621{,}773{,}516{,}800{,}000{,}000{,}000,
--   $$
--
--   there exist **odd** primes $p, q, r$ with $n = p + q + r$.
--
--   This is the all-odd strengthening of the verified ternary range: writing $n = 3 + (n-3)$ requires an odd-prime partition of the even number $n - 3$ — confirmed throughout the range by the partition data of Oliveira e Silva–Herzog–Pardi.
-- source:
--   Helfgott–Platt, arXiv:1305.3062v2 (verified range), combined with the odd-prime-partition fact implicit in the OeS–Herzog–Pardi binary data, doi:10.1090/s0025-5718-2013-02787-1

import Mathlib

namespace WeakGoldbach

theorem verified_three_odd_primes_to_8875e30 (n : ℕ)
    (hlo : 9 ≤ n) (hhi : n ≤ 8875694145621773516800000000000) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  sorry

end WeakGoldbach
