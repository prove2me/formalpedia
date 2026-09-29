-- Prove2me | Theorems.Thm_SpikeOrigin_sharp_degeneracy
-- name    : SpikeOrigin.sharp_degeneracy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:24.746928+00:00
-- url     : https://prove2.me/theorems/d0429f69-76d1-464b-b487-b95454b61929
-- title:
--   Sharp degeneracy.
-- statement:
--   **Sharp degeneracy.**  For a `96`-bit modulus, every window point at normalised
--   position `u = (j − s)/(2s) ≤ 0.1123` has a sub-`2⁹⁵` residue.  The constant `0.1123` is
--   within `10⁻⁴` of the continuum optimum `(√6 − 2)/4`.
--
--   ```lean
--   theorem SpikeOrigin.sharp_degeneracy{N j : ℕ} (hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96)
--       (hj : Nat.sqrt N < j) (hu : 10000 * (j - Nat.sqrt N) ≤ 2246 * Nat.sqrt N) :
--       resid N j < 2 ^ 95 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginSharp.lean#L28

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

theorem SpikeOrigin.sharp_degeneracy{N j : ℕ} (hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96)
    (hj : Nat.sqrt N < j) (hu : 10000 * (j - Nat.sqrt N) ≤ 2246 * Nat.sqrt N) :
    resid N j < 2 ^ 95 := by sorry
