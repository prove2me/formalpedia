-- Prove2me | Theorems.Thm_SpikeOrigin_card_band_succ
-- name    : SpikeOrigin.card_band_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:01:18.470681+00:00
-- url     : https://prove2.me/theorems/2d97d5fa-88f3-4955-8d66-e581875d784f
-- title:
--   The band populations telescope: `#{bitlen v ≤ b} + #{bitlen v = b+1} = #{bitlen v ≤ b+1}`.
-- statement:
--   The band populations telescope: `#{bitlen v ≤ b} + #{bitlen v = b+1} = #{bitlen v ≤ b+1}`.
--
--   ```lean
--   theorem SpikeOrigin.card_band_succ(N b : ℕ) :
--       ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
--           (fun j => (resid N j).size ≤ b)).card
--         + ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
--           (fun j => (resid N j).size = b + 1)).card
--         = ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
--           (fun j => (resid N j).size ≤ b + 1)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginSharp.lean#L98

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




/-! ## Deterministic band histogram -/

theorem SpikeOrigin.card_band_succ(N b : ℕ) :
    ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => (resid N j).size ≤ b)).card
      + ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => (resid N j).size = b + 1)).card
      = ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => (resid N j).size ≤ b + 1)).card := by sorry
