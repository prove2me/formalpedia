-- Prove2me | solution 1 for ShorIrreducible.card_multiples_range
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:15:09.432134+00:00
-- url     : https://prove2.me/submissions/69f502d2-f96e-4c2a-a4bd-c1545a35c6a7

-- Sol generated from Novelty/ShorQFTOutput.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutput

/-! # The QFT output of the comb: exactly `r` flat peaks, and why truncation fails

This file computes the *output* of the quantum Fourier transform on the periodic
comb `[x ≡ x₀ mod r]` of a register of size `Q = r * m`, and derives the
sampling-level obstruction to any classical emulation that keeps only
polynomially many amplitudes.

Main results:

* `combDFT_eq` : the Fourier sum of the comb,
  `∑_{t<m} ζ_Q^{(j + r t) y} = m ζ_Q^{j y}` if `m ∣ y` and `0` otherwise:
  the output is supported on the `r` multiples of `m = Q / r` and nowhere else;
* `norm_combDFT` : all `r` surviving amplitudes have the *same* modulus `m` —
  the output comb is flat, not "nearly a single basis state";
* `qftCombProb_apply` and `sum_qftCombProb` : the measured output distribution
  is uniform on those `r` frequencies;
* `tvDist_ge_sum_sub` and `tvDist_qftComb_ge` : **any** classical sampler whose
  output distribution is supported on a set `S` differs from the ideal Shor
  output distribution in total variation by at least `1 - |S| / r`; with
  `2 * |S| ≤ r` the distance is at least `1/2`
  (`tvDist_qftComb_ge_half`).  A truncated emulation fails catastrophically
  rather than approximately.
-/

open Finset
open scoped Real

open ShorIrreducible

/-! ## The Fourier transform of a comb -/








/-! ## The output distribution of Shor's algorithm -/





/-! ## Total-variation failure of any small-support sampler -/








open ShorIrreducible in
theorem solution{r m : ℕ} (hm : 0 < m) :
    ((Finset.range (r * m)).filter fun y => m ∣ y).card = r := by
  classical
  have himg : ((Finset.range (r * m)).filter fun y => m ∣ y)
      = (Finset.range r).image (fun k => m * k) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hy, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      by_contra hk
      push_neg at hk
      have : r * m ≤ m * k := by
        calc r * m = m * r := by ring
          _ ≤ m * k := Nat.mul_le_mul_left m hk
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, ⟨k, rfl⟩⟩
      calc m * k < m * r := by
            exact mul_lt_mul_of_pos_left hk hm
        _ = r * m := by ring
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left hm hab),
    Finset.card_range]
