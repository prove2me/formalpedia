-- Prove2me | solution 1 for ScaleSmoothness.dial_eq_zero_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:32:55.042176+00:00
-- url     : https://prove2.me/submissions/2dfd058c-ed59-40e4-8416-eb703c275935

-- Sol generated from NumberTheory/QRDialLocalStatistics.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics

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


theorem dial_def (p : ℕ) [NeZero p] (N : ZMod p) :
    dial p N = #(univ.filter fun x : ZMod p => x ^ 2 = N) := rfl


variable (p : ℕ) [Fact p.Prime]







/-- The dial vanishes exactly on the nonsquares. -/
theorem dial_eq_zero_iff {N : ZMod p} : dial p N = 0 ↔ ¬ IsSquare N := by
  rw [dial_def, card_eq_zero, filter_eq_empty_iff]
  constructor
  · rintro h ⟨r, rfl⟩
    exact h (mem_univ r) (by ring)
  · intro h x _ hx
    exact h ⟨x, by rw [← hx]; ring⟩





/-! ### Moments of the dial -/




/-! ### The multiplicative local correction factor -/











open ScaleSmoothness in
theorem solution{N : ZMod p} (h : ¬ IsSquare N) : dial p N = 0 :=
  (dial_eq_zero_iff p).2 h
