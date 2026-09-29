-- Prove2me | solution 3 for flt_odd_prime_ge_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T09:01:18.708587+00:00
-- url     : https://prove2.me/submissions/cbcfa792-b5c1-4fe8-959c-6fb546b82298
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_bp_flt_for_p_ge_5


theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p :=
  bp_flt_for_p_ge_5 p hp h5 a b c ha hb hc
