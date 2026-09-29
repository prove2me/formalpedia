-- Prove2me | solution 1 for ScaleSmoothness.sum_localFactor_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:08:28.246167+00:00
-- url     : https://prove2.me/submissions/f9f4af9d-210e-466d-8b7a-85c6c734e13c

-- Sol generated from NumberTheory/QRDialLocalStatistics.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Theorems.Thm_ScaleSmoothness_sum_dial
import Theorems.Thm_ScaleSmoothness_sum_dial_sq
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
theorem solution(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∑ N : ZMod p, (localFactor p N) ^ 2 = (p : ℚ) + 1 / ((p : ℚ) - 1) := by
  have h3 : (3 : ℕ) ≤ p := three_le_of_ne_two p hp
  have hpq : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  have hne : ((p : ℚ) - 1) ≠ 0 := by linarith
  have hsum : ∑ N : ZMod p, ((dial p N : ℚ)) = (p : ℚ) := by
    have := sum_dial p
    calc ∑ N : ZMod p, ((dial p N : ℚ)) = ((∑ N : ZMod p, dial p N : ℕ) : ℚ) := by push_cast; ring
      _ = (p : ℚ) := by rw [this]
  have hsum2 : ∑ N : ZMod p, ((dial p N : ℚ)) ^ 2 = 2 * (p : ℚ) - 1 := by
    have h := sum_dial_sq p hp
    have h2 : (1 : ℕ) ≤ 2 * p := by omega
    calc ∑ N : ZMod p, ((dial p N : ℚ)) ^ 2
        = ((∑ N : ZMod p, (dial p N) ^ 2 : ℕ) : ℚ) := by push_cast; ring
      _ = ((2 * p - 1 : ℕ) : ℚ) := by rw [h]
      _ = 2 * (p : ℚ) - 1 := by
          have : ((2 * p - 1 : ℕ) : ℚ) = ((2 * p : ℕ) : ℚ) - ((1 : ℕ) : ℚ) := by
            rw [Nat.cast_sub h2]
          rw [this]; push_cast; ring
  have expand : ∀ N : ZMod p, (localFactor p N) ^ 2 =
      ((p : ℚ) ^ 2 - 2 * (p : ℚ) * (dial p N : ℚ) + (dial p N : ℚ) ^ 2) / ((p : ℚ) - 1) ^ 2 := by
    intro N; rw [localFactor, div_pow]; ring_nf
  simp only [expand, ← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hsum2,
    Finset.sum_const, Finset.card_univ, ZMod.card]
  field_simp
  ring
