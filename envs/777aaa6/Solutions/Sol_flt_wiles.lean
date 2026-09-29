-- Prove2me | solution 1 for flt_wiles
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-15T06:42:15.167655+00:00
-- url     : https://prove2.me/submissions/069a1775-9840-4fc0-8a3e-c613ca563c79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_flt_odd_prime_coprime_reduction
import Theorems.Thm_flt_wiles_coprime

-- Reduce to coprime triples using the already-proved reduction lemma,
-- then dispatch to the Wiles proof for coprime FLT.
theorem solution (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p :=
  flt_odd_prime_coprime_reduction p hp (by omega) a b c ha hb hc
    (fun a' b' c' ha' hb' hc' hab' hbc' hac' =>
      flt_wiles_coprime p hp h7 a' b' c' ha' hb' hc' hab' hbc' hac')
