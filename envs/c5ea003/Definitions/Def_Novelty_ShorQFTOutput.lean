-- Prove2me | Definitions.Def_Novelty_ShorQFTOutput
-- name    : Novelty_ShorQFTOutput
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:58:46.426103+00:00
-- url     : https://prove2.me/theorems/9d873f3a-c6a5-47e3-9d6a-cccb81923a39
-- title:
--   Aether Catalog definitions — Novelty_ShorQFTOutput
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShorQFTOutput`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShorQFTOutput.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ShorCombState

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

namespace ShorIrreducible

/-! ## The Fourier transform of a comb -/

/-- The standard primitive `n`-th root of unity. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / n)




/-- The Fourier sum of the comb `{ j + r t : t < m }` at frequency `y`. -/
noncomputable def combDFT (r m j y : ℕ) : ℂ :=
  ∑ t ∈ Finset.range m, zeta (r * m) ^ ((j + r * t) * y)



/-! ## The output distribution of Shor's algorithm -/

/-- The measurement distribution of the QFT output of the comb: uniform on the
`r` multiples of `m = Q / r`. -/
noncomputable def qftCombProb (r m : ℕ) : ℕ → ℝ := fun y => if m ∣ y then (r : ℝ)⁻¹ else 0




/-! ## Total-variation failure of any small-support sampler -/

/-- Total variation distance between two mass functions on a finite type. -/
noncomputable def tvDist {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|


/-- The `r` peak frequencies, as a subset of the register. -/
noncomputable def peakSet (r m : ℕ) : Finset (Fin (r * m)) :=
  (univ : Finset (Fin (r * m))).filter fun y => m ∣ (y : ℕ)




end ShorIrreducible


