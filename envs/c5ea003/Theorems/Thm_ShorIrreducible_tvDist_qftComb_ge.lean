-- Prove2me | Theorems.Thm_ShorIrreducible_tvDist_qftComb_ge
-- name    : ShorIrreducible.tvDist_qftComb_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:14:25.850312+00:00
-- url     : https://prove2.me/theorems/4aae44f1-e28c-4694-ab26-dd130bbf7491
-- title:
--   **Every small-support classical sampler is far from Shor's output
-- statement:
--   **Every small-support classical sampler is far from Shor's output
--   distribution.**  If a purported classical emulation only ever outputs
--   frequencies in a set `S`, its total variation distance from the ideal QFT output
--   distribution is at least `1 - |S| / r`.
--
--   ```lean
--   theorem ShorIrreducible.tvDist_qftComb_ge{r m : ℕ} (hr : 0 < r) (hm : 0 < m) (q : Fin (r * m) → ℝ)
--       (hq : ∑ y, q y = 1) (S : Finset (Fin (r * m))) (hsupp : ∀ y ∉ S, q y = 0) :
--       1 - (S.card : ℝ) / r ≤ tvDist (fun y : Fin (r * m) => qftCombProb r m (y : ℕ)) q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorQFTOutput.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorQFTOutput.lean#L199

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





/-! ## Total-variation failure of any small-support sampler -/

theorem ShorIrreducible.tvDist_qftComb_ge{r m : ℕ} (hr : 0 < r) (hm : 0 < m) (q : Fin (r * m) → ℝ)
    (hq : ∑ y, q y = 1) (S : Finset (Fin (r * m))) (hsupp : ∀ y ∉ S, q y = 0) :
    1 - (S.card : ℝ) / r ≤ tvDist (fun y : Fin (r * m) => qftCombProb r m (y : ℕ)) q := by sorry
