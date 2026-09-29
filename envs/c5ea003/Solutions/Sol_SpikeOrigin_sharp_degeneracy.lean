-- Prove2me | solution 1 for SpikeOrigin.sharp_degeneracy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:12:08.215675+00:00
-- url     : https://prove2.me/submissions/28fbc9d3-d15e-4956-a396-bb6166cc1818

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
theorem solution{N j : ℕ} (hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96)
    (hj : Nat.sqrt N < j) (hu : 10000 * (j - Nat.sqrt N) ≤ 2246 * Nat.sqrt N) :
    resid N j < 2 ^ 95 := by
  set s := Nat.sqrt N with hs
  set d := j - s with hd
  have hjs : j = s + d := by omega
  have hsq : s * s ≤ N := Nat.sqrt_le N
  have hv : resid N j ≤ 2 * s * d + d * d := by
    have hj2 : j ^ 2 = s * s + (2 * s * d + d * d) := by rw [hjs]; ring
    have : resid N j = s * s + (2 * s * d + d * d) - N := by rw [resid, hj2]
    omega
  have hkey : 100000000 * (2 * s * d + d * d) ≤ 49964516 * (s * s) := by nlinarith
  have hNs : 49964516 * (s * s) ≤ 49964516 * N := Nat.mul_le_mul_left _ hsq
  have hbound : 100000000 * resid N j ≤ 49964516 * N :=
    le_trans (Nat.mul_le_mul_left _ hv) (le_trans hkey hNs)
  have h96 : (2 : ℕ) ^ 96 = 2 * 2 ^ 95 := by ring
  omega
