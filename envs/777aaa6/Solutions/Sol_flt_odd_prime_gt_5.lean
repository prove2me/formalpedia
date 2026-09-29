-- Prove2me | solution 1 for flt_odd_prime_gt_5
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-15T06:39:50.651896+00:00
-- url     : https://prove2.me/submissions/c663a126-a50f-4d81-b2c7-2c7ae267ec4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_flt_wiles

-- FLT for primes p≥7 follows from Wiles' theorem (Wiles-Taylor 1995).
-- For regular primes, Kummer's earlier proof also works, but Wiles subsumes it.
theorem solution (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p :=
  flt_wiles p hp h7 a b c ha hb hc
