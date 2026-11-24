-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_two_pow_twenty_three
-- name    : syracuse_no_cycle_below_two_pow_twenty_three
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T08:12:47.82383+00:00
-- url     : https://prove2.me/theorems/3200d4f9-6281-4ae0-b7a3-d564488a54d7
-- title:
--   No nontrivial Syracuse cycle contains an entry below 8,388,608
-- statement:
--   Let $T(m)$ be the odd part of $3m+1$. For any positive $m<2^{23}=8{,}388{,}608$ and $p>0$, if $T^p(m)=m$, then $m=1$. A Lean-kernel-checked finite descent certificate for the shortcut Collatz map supplies the cutoff. It applies to every positive return time.
-- source:
--   Dyadic affine descent verification for the shortcut map, for the Collatz residual https://prove2.me/theorems/8c018c44-08ba-40b6-b2e5-ef0d57d499c8.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_no_cycle_below_two_pow_twenty_three (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hlt : m < 8388608)
    (hcyc : syracuseStep^[p] m = m) : m = 1 := by sorry
