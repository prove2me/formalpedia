-- Prove2me | solution 2 for flt_odd_prime_gt_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T09:01:18.676624+00:00
-- url     : https://prove2.me/submissions/f2cf7cd8-dffd-4334-88ae-89916eed00f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_flt_wiles


theorem solution (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p :=
  flt_wiles p hp h7 a b c ha hb hc
