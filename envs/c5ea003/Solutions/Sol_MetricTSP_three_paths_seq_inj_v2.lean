-- Prove2me | solution 1 for MetricTSP.three_paths_seq_inj_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-06T01:43:16.698442+00:00
-- url     : https://prove2.me/submissions/33d749e3-21b3-4767-bf83-401170f6a36c

import Mathlib
import Definitions.Def_MetricTSP_three_paths_seq

open MetricTSP in
theorem solution (k : ℕ) (hk : 1 ≤ k) (p q m m2 : ℕ)
    (hp : p < 3) (hq : q < 3) (hm : m ≤ k+1) (hm2 : m2 ≤ k+1)
    (h : tpSeq k p m = tpSeq k q m2) :
    m = m2 ∧ (p = q ∨ m = 0 ∨ m = k+1) := by
  -- the underlying index of `tpSeq`, with the (inert) modulus removed
  have key : ∀ r n : ℕ, r < 3 → n ≤ k + 1 →
      (tpSeq k r n).val =
        if n = 0 then 0 else if n = k + 1 then 3 * k + 1 else 1 + r * k + (n - 1) := by
    intro r n hr hn
    unfold tpSeq
    split_ifs with a b
    · rfl
    · rfl
    · have hrk : r * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
      exact Nat.mod_eq_of_lt (by omega)
  have hval := congrArg Fin.val h
  rw [key p m hp hm, key q m2 hq hm2] at hval
  interval_cases p <;> interval_cases q <;> split_ifs at hval <;> omega
