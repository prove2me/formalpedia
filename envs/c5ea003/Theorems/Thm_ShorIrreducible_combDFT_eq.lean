-- Prove2me | Theorems.Thm_ShorIrreducible_combDFT_eq
-- name    : ShorIrreducible.combDFT_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:09:47.827389+00:00
-- url     : https://prove2.me/theorems/d3791b79-5350-4e0d-b1d1-d0c18b565740
-- title:
--   The Fourier transform of a periodic comb is a periodic comb.
-- statement:
--   **The Fourier transform of a periodic comb is a periodic comb.**  The
--   amplitude vanishes unless the frequency is a multiple of `m = Q / r`, and on
--   each of those `r` frequencies it has modulus `m`.
--
--   ```lean
--   theorem ShorIrreducible.combDFT_eq{r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
--       combDFT r m j y = if m ∣ y then (m : ℂ) * zeta (r * m) ^ (j * y) else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorQFTOutput.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorQFTOutput.lean#L55

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

theorem ShorIrreducible.combDFT_eq{r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
    combDFT r m j y = if m ∣ y then (m : ℂ) * zeta (r * m) ^ (j * y) else 0 := by sorry
