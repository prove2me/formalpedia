-- Prove2me | Theorems.Thm_SpikeOrigin_fraction_bridge
-- name    : SpikeOrigin.fraction_bridge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:26.816174+00:00
-- url     : https://prove2.me/theorems/fb4d7e88-171d-4a58-93dc-6fb833e16fad
-- title:
--   Normalised form of the bridge: the exact discrete excluded fraction and the continuum
-- statement:
--   Normalised form of the bridge: the exact discrete excluded fraction and the continuum
--   crossing position agree to `3/s`.  For `96`-bit moduli `s ≥ 2⁴⁷`, so the agreement is to
--   about fourteen decimal digits.
--
--   ```lean
--   theorem SpikeOrigin.fraction_bridge{N : ℕ} (hlo : 2 ^ 95 ≤ N) :
--       |((Nat.sqrt (N + 2 ^ 95 - 1) : ℝ) - (Nat.sqrt N : ℝ)) / (2 * (Nat.sqrt N : ℝ))
--         - crossingPos (N : ℝ)| ≤ 3 / (Nat.sqrt N : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginBridge.lean#L87

-- Thm stub generated from Cryptography/SpikeOriginBridge.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
/-
# Discrete–continuum bridge for the excluded fraction

Continuation of `Cryptography.SpikeOriginCounting`.

The exact integer count of the sub-`2⁹⁵` (tiny-residue) window points is
`m − s` with `m = ⌊√(N + 2⁹⁵ − 1)⌋`, `s = ⌊√N⌋` (`card_lowBand`), while the continuum model
predicts the fraction `u₀(N) = (√(1 + 2⁹⁵/N) − 1)/2` (`crossingPos`).  Here the two are
compared:

* `crossingPos_eq` rewrites `u₀` as `(√(N + 2⁹⁵) − √N)/(2√N)`;
* `count_bridge` shows the integer count differs from the continuum length by at most `2`;
* `fraction_bridge` turns this into `|(m − s)/(2s) − u₀(N)| ≤ 3/s`.

At `96` bits `s ≥ 2⁴⁷`, so the discrete and continuum excluded fractions agree to about
fourteen decimal digits: discretisation can never explain a discrepancy in a fitted edge
weight.
-/

open SpikeOrigin

/-! ## Real bounds for the integer square root -/




/-! ## The crossing position as a difference of square roots -/


/-! ## The bridge -/

theorem SpikeOrigin.fraction_bridge{N : ℕ} (hlo : 2 ^ 95 ≤ N) :
    |((Nat.sqrt (N + 2 ^ 95 - 1) : ℝ) - (Nat.sqrt N : ℝ)) / (2 * (Nat.sqrt N : ℝ))
      - crossingPos (N : ℝ)| ≤ 3 / (Nat.sqrt N : ℝ) := by sorry
