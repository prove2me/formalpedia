-- Prove2me | Theorems.Thm_SpikeOrigin_sharp_constant_witness
-- name    : SpikeOrigin.sharp_constant_witness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:10.190174+00:00
-- url     : https://prove2.me/theorems/927b139a-b578-4bf9-8655-a6539b5fe214
-- title:
--   The constant cannot be pushed past `0.2072`.
-- statement:
--   **The constant cannot be pushed past `0.2072`.**  There is a `96`-bit modulus with a
--   *full-size* residue already at normalised position `u ≤ 0.2072`, just below the continuum
--   endpoint `(√2 − 1)/2 = 0.20711…`.
--
--   ```lean
--   theorem SpikeOrigin.sharp_constant_witness:
--       ∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ Nat.sqrt N < j ∧ j ≤ 3 * Nat.sqrt N ∧
--         10000 * (j - Nat.sqrt N) ≤ 2072 * (2 * Nat.sqrt N) ∧ 2 ^ 95 ≤ resid N j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginSharp.lean#L49

-- Thm stub generated from Cryptography/SpikeOriginSharp.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
/-
# Sharp constants and the deterministic band histogram

Continuation of `Cryptography.SpikeOriginDegeneracy`, `…Bands`, `…Counting`.

Two further steps of the programme:

* **Sharp discrete degeneracy constant.**  The degeneracy of the "`v ≥ 2⁹⁵`" clause was
  proved above for the first decile `u ≲ 0.1`.  Here it is pushed to `u ≤ 0.1123`
  (`sharp_degeneracy`), which is essentially the continuum optimum
  `(√6 − 2)/4 = 0.11237…`, and shown to be impossible beyond `u = 0.2072`
  (`sharp_constant_witness`) — the other continuum endpoint being
  `(√2 − 1)/2 = 0.20711…`.  So the exact discrete threshold is bracketed by the same two
  quadratic irrationalities that bound the crossing curve (`discrete_threshold_bracket`).

* **Deterministic band histogram.**  Because the residue is strictly increasing, the number
  of window positions with `bitlen v ≤ b` is an explicit difference of integer square roots
  (`card_sizeLe`), and the individual band populations telescope (`card_band_succ`,
  `card_band_formula`).  The band decomposition of a Fermat window carries no stochastic
  content at all: it is a function of `N` alone.
-/

open SpikeOrigin

/-! ## Sharp constant for the degeneracy -/

theorem SpikeOrigin.sharp_constant_witness:
    ∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ Nat.sqrt N < j ∧ j ≤ 3 * Nat.sqrt N ∧
      10000 * (j - Nat.sqrt N) ≤ 2072 * (2 * Nat.sqrt N) ∧ 2 ^ 95 ≤ resid N j := by sorry
