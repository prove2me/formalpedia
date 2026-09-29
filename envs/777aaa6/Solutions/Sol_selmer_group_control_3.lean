-- Prove2me | solution 3 for selmer_group_control
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T09:01:18.661135+00:00
-- url     : https://prove2.me/submissions/aa364564-b9c4-43e9-94a7-64460a799ded
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_iwasawa_freeness


theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) :
    False :=
  iwasawa_freeness p hp h5 a b c ha hb hc hab hbc hac heq
