-- Prove2me | solution 1 for MachineLearning.WignerSemicircle.scMoment_le_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:18:31.400285+00:00
-- url     : https://prove2.me/submissions/dc726b7d-d79a-4e39-9d43-27877f3f114b

-- Sol generated from MachineLearning/WignerSemicircle/Moments.lean
import Mathlib
import Definitions.Def_MachineLearning_WignerSemicircle_Moments
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Moments of the Wigner Semicircle Distribution

The Wigner semicircle law states that the empirical spectral distribution of a
Wigner random matrix converges weakly to the semicircle distribution.  The
combinatorial heart of the *moment method* proof is the following fact: the
moments of the (standard, radius-2) semicircle distribution are exactly the
**Catalan numbers**,

  m_{2k} = C_k,   m_{2k+1} = 0,

and these numbers satisfy the Catalan recurrence

  C_{n+1} = ∑_{i=0}^{n} C_i · C_{n-i}.

This recurrence is precisely the recurrence one obtains for the limiting expected
traces `(1/N) E tr(W^{2k})` of a Wigner ensemble via the non-crossing pair
partition (Dyck path) enumeration.  This file develops this moment sequence as a
real-valued function on `ℕ` and proves the chain of facts that make it the unique
candidate limit in the moment method.

## Main results

- `scMoment_zero`        — the 0-th moment is 1 (total mass).
- `scMoment_odd`         — all odd moments vanish (symmetry).
- `scMoment_two_mul`     — the `2k`-th moment equals `catalan k`.
- `scMoment_recurrence`  — the Wigner/Catalan moment recurrence.
- `scMoment_centralBinom`— closed form via the central binomial coefficient.
- `scMoment_le_four_pow` — the Carleman-type growth bound `m_{2k} ≤ 4^k`,
                           which guarantees the moment problem is determinate.
- concrete values `scMoment_two`, `scMoment_four`, `scMoment_six`.
-/

open MachineLearning.WignerSemicircle

open scoped BigOperators




/-- The even moment `m_{2k}` equals the `k`-th Catalan number. -/
theorem scMoment_two_mul (k : ℕ) : scMoment (2 * k) = (catalan k : ℝ) := by
  rw [scMoment, if_pos (even_two_mul k)]
  congr 2
  omega









open MachineLearning.WignerSemicircle in
theorem solution(k : ℕ) : scMoment (2 * k) ≤ (4 : ℝ) ^ k := by
  rw [scMoment_two_mul]
  have hcat : catalan k ≤ Nat.centralBinom k := by
    have h := succ_mul_catalan_eq_centralBinom k
    calc catalan k ≤ (k + 1) * catalan k := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
      _ = Nat.centralBinom k := h
  have hcb : Nat.centralBinom k ≤ 4 ^ k := by
    have hsum : ∑ i ∈ Finset.range (2 * k + 1), (2 * k).choose i = 2 ^ (2 * k) :=
      Nat.sum_range_choose (2 * k)
    have hmem : k ∈ Finset.range (2 * k + 1) := by
      simp only [Finset.mem_range]; omega
    have hle : (2 * k).choose k ≤ ∑ i ∈ Finset.range (2 * k + 1), (2 * k).choose i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
    rw [hsum] at hle
    calc Nat.centralBinom k = (2 * k).choose k := rfl
      _ ≤ 2 ^ (2 * k) := hle
      _ = 4 ^ k := by rw [pow_mul]; norm_num
  have : catalan k ≤ 4 ^ k := le_trans hcat hcb
  calc (catalan k : ℝ) ≤ ((4 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    _ = (4 : ℝ) ^ k := by push_cast; ring
