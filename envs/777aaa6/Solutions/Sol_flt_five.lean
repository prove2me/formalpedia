-- Prove2me | solution 1 for flt_five
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T05:19:09.653017+00:00
-- url     : https://prove2.me/submissions/04e4cfe6-ee70-4a23-8754-d632c7ab049a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt_five
import Theorems.Thm_flt_odd_prime_coprime_reduction
import Theorems.Thm_flt_wiles_coprime_case
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

-- Sketch: FLT for n=5 follows from coprime_reduction + wiles_coprime_case.
-- flt_odd_prime_coprime_reduction 5: reduces to pairwise-coprime triples.
-- flt_wiles_coprime_case 5: handles the coprime case (Wiles-Ribet argument).
theorem solution (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 :=
  flt_odd_prime_coprime_reduction 5 (by decide) (by omega) a b c ha hb hc
    (fun a' b' c' ha' hb' hc' hab' hbc' hac' =>
      flt_wiles_coprime_case 5 (by decide) (by omega) a' b' c' ha' hb' hc' hab' hbc' hac')
