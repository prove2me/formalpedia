-- Prove2me | Theorems.Thm_ScaleSmoothness_localFactor_lt_of_qr
-- name    : ScaleSmoothness.localFactor_lt_of_qr
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:52:07.354574+00:00
-- url     : https://prove2.me/theorems/3bade24a-7859-45a9-bf88-6b5a5b056613
-- title:
--   The QR dial, quantitatively.
-- statement:
--   **The QR dial, quantitatively.**  A residue is *harder* to make smooth exactly
--   when it is a quadratic residue: the local factor at a residue is strictly smaller
--   than at a nonresidue.
--
--   ```lean
--   theorem ScaleSmoothness.localFactor_lt_of_qr(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {N N' : ZMod p}
--       (hN : dial p N = 2) (hN' : dial p N' = 0) : localFactor p N < localFactor p N' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QRDialLocalStatistics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QRDialLocalStatistics.lean#L224

-- Thm stub generated from NumberTheory/QRDialLocalStatistics.lean
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




variable (p : ℕ) [Fact p.Prime]












/-! ### Moments of the dial -/




/-! ### The multiplicative local correction factor -/

theorem ScaleSmoothness.localFactor_lt_of_qr(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {N N' : ZMod p}
    (hN : dial p N = 2) (hN' : dial p N' = 0) : localFactor p N < localFactor p N' := by sorry
