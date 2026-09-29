-- Prove2me | Theorems.Thm_ShorIrreducible_qftCombProb_apply
-- name    : ShorIrreducible.qftCombProb_apply
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:14:35.285721+00:00
-- url     : https://prove2.me/theorems/8a299eae-2f09-4817-8052-a4ecfa8998f5
-- title:
--   The probability of the frequency `y` is the squared modulus of the
-- statement:
--   The probability of the frequency `y` is the squared modulus of the
--   normalized output amplitude `(r m²)^{-1/2} · combDFT`.
--
--   ```lean
--   theorem ShorIrreducible.qftCombProb_apply{r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
--       ((Real.sqrt ((r : ℝ) * m * m))⁻¹ * ‖combDFT r m j y‖) ^ 2 = qftCombProb r m y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorQFTOutput.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorQFTOutput.lean#L103

-- Thm stub generated from Novelty/ShorQFTOutput.lean
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

theorem ShorIrreducible.qftCombProb_apply{r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
    ((Real.sqrt ((r : ℝ) * m * m))⁻¹ * ‖combDFT r m j y‖) ^ 2 = qftCombProb r m y := by sorry
