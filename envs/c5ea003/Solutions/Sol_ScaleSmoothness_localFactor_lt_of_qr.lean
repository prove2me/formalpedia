-- Prove2me | solution 1 for ScaleSmoothness.localFactor_lt_of_qr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:26:50.367308+00:00
-- url     : https://prove2.me/submissions/f1f1df19-7909-4027-84f6-3ab684a21653

-- Sol generated from NumberTheory/QRDialLocalStatistics.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Theorems.Thm_ScaleSmoothness_localFactor_of_dial_two
import Theorems.Thm_ScaleSmoothness_localFactor_of_dial_zero
import Theorems.Thm_ScaleSmoothness_three_le_of_ne_two

/-!
# The quadratic-residue dial of `x² − N`: exact local statistics

This file is the rigorous local half of the round-73 #4 (exp 562) finding
**SCALE-SMOOTHNESS-DEVIATION / RANDOM-AT-SCALE**: numerically the `B`-smoothness
probability of the quadratic-sieve polynomial `x² − N` was found to be
indistinguishable from that of size-matched random integers
(`r(u) = 1.011, 0.949, 0.900, 1.200` at `u ≈ 5.96, 6.95, 7.93, 8.26`, all
confidence intervals covering `1`, tightest bound `|r − 1| ≤ 0.217`), while a
*per-`N`* overdispersion `D = 1.61 [1.50, 1.73]` and a QR-dial correlation were
observed at the low-`u` face.

The mechanism behind both observations is completely local and completely
computable: for a prime `p` the polynomial `x² − N` hits `0 mod p` on

  `dial p N := #{x ∈ ZMod p | x² = N}`

residues instead of the "random" single residue.  This file computes the
distribution of that dial exactly.

## Main results

* `dial_of_sq`, `dial_eq_two_iff`, `dial_eq_zero_iff`, `dial_zero` — the
  **dichotomy**: for an odd prime `p` the dial is `2` on nonzero squares, `0` on
  nonsquares, and `1` at `N = 0`.
* `sum_dial` — **first moment is exactly random**: `∑_N dial p N = p`, i.e. the
  dial has mean exactly `1`, the same local density as a random integer.  This
  is the exact statement that quadratic structure gives *no* first-order
  smoothness edge.
* `sum_dial_sq` — **second moment**: `∑_N (dial p N)² = 2p − 1`.
* `localFactor` — the induced multiplicative correction
  `(p − dial p N)/(p − 1)` to the local non-divisibility density, and
  `sum_localFactor` (mean exactly `1`), `sum_localFactor_sq`
  (`= p + 1/(p−1)`), and `sum_localFactor_centred_sq` (variance exactly
  `1/(p(p−1))` per prime).

The variance `1/(p(p−1))` is the seed of the observed per-`N` overdispersion;
it is summed over primes in `Catalog.NumberTheory.ScaleSmoothnessDispersion`.
-/

open ScaleSmoothness

open Finset




variable (p : ℕ) [Fact p.Prime]












/-! ### Moments of the dial -/




/-! ### The multiplicative local correction factor -/











open ScaleSmoothness in
theorem solution(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {N N' : ZMod p}
    (hN : dial p N = 2) (hN' : dial p N' = 0) : localFactor p N < localFactor p N' := by
  have h3 : (3 : ℕ) ≤ p := three_le_of_ne_two p hp
  have hpq : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [localFactor_of_dial_two p hN, localFactor_of_dial_zero p hN']
  exact div_lt_div_of_pos_right (by linarith) hden
