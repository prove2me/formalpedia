-- Prove2me | solution 1 for SpikeOrigin.sharp_constant_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:12:07.778594+00:00
-- url     : https://prove2.me/submissions/df5bc721-b49e-434d-b553-3b896edb9495

-- Sol generated from Cryptography/SpikeOriginSharp.lean
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





open SpikeOrigin in
theorem solution:
    ∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ Nat.sqrt N < j ∧ j ≤ 3 * Nat.sqrt N ∧
      10000 * (j - Nat.sqrt N) ≤ 2072 * (2 * Nat.sqrt N) ∧ 2 ^ 95 ≤ resid N j := by
  refine ⟨199032864766431 * 199032864766431, 281512083925640, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · rw [Nat.sqrt_eq]; norm_num
  · rw [Nat.sqrt_eq]; norm_num
  · rw [Nat.sqrt_eq]; norm_num
  · rw [resid]
    have e : (281512083925640 : ℕ) ^ 2 = 79249053396156578873049409600 := by norm_num
    have f : (2 : ℕ) ^ 95 = 39614081257132168796771975168 := by norm_num
    have g : (199032864766431 : ℕ) * 199032864766431 =
        39614081257132410564184477761 := by norm_num
    omega
