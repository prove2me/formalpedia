-- Prove2me | solution 1 for ShorIrreducible.card_peakSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:16:49.538981+00:00
-- url     : https://prove2.me/submissions/ce924303-0611-4d33-bb0d-ba60b78d6848

-- Sol generated from Novelty/ShorQFTOutput.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutput
import Theorems.Thm_ShorIrreducible_card_multiples_range

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
theorem solution{r m : ℕ} (hm : 0 < m) : (peakSet r m).card = r := by
  classical
  have himg : (peakSet r m).image (fun y : Fin (r * m) => (y : ℕ))
      = (Finset.range (r * m)).filter fun y => m ∣ y := by
    ext y
    simp only [peakSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.isLt, hz⟩
    · rintro ⟨hy, hdvd⟩
      exact ⟨⟨y, hy⟩, hdvd, rfl⟩
  rw [← Finset.card_image_of_injective _ (Fin.val_injective), himg, card_multiples_range hm]
