-- Prove2me | solution 1 for SpikeOrigin.resid_mul_25_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:07:40.432534+00:00
-- url     : https://prove2.me/submissions/9ec9c7a2-cbbd-491d-9d61-b1341934a4aa

-- Sol generated from Cryptography/SpikeOriginDegeneracy.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
/-
# Spike-origin degeneracy: the left-edge decile of a Fermat window carries only tiny residues

Setting (exp 589 / paper 239).  For a modulus `N` one scans trial points `j` in the
Fermat-style window `j ∈ (s, 3s]`, `s = ⌊√N⌋`, and records the residue `v = j² − N`.
Positions are normalised to `u = (j − s) / (2s) ∈ (0, 1]`.  The empirical study reports a
left-edge spike concentrated in the *first decile* `D1 = {u ≲ 1/10}` and asks whether the
"exclude `v < 2⁹⁵`" clause can discriminate anything there.

This file proves, by exact arithmetic, that the clause is **degenerate**: every `D1` point
of a `96`-bit modulus has `v < 2⁹⁵`, i.e. `bitlen v ≤ 95`, so the exclusion removes
*100 %* of the `D1` mass by geometry alone.  The mechanism is scale free
(`resid_lt_of_firstDecile_scalefree`: `v < 0.45 · N`) and it is **sharp**: past position
`u ≈ 0.21` the residue is provably full size, and in the continuum the exact transition
point is the crossing curve `u₀(N) = (√(1 + 2⁹⁵/N) − 1)/2`, which is pinned to the interval
`((√6 − 2)/4, (√2 − 1)/2] ⊂ (0.1123, 0.2072]`.  In particular the decile boundary `1/10`
lies *strictly below* the smallest possible crossing `(√6 − 2)/4 = 0.11237…`, which is the
structural reason for the degeneracy — and it also explains the reported kept-support left
edge `u ≈ 0.114`.
-/

open SpikeOrigin

/-! ## Discrete layer: window, residue, first decile -/










/-! ## Continuum layer: the exact crossing curve and its sharp interval -/

open Real








open SpikeOrigin in
theorem solution{N j : ℕ} (h : FirstDecile N j) :
    25 * resid N j ≤ 11 * N + 48 * Nat.sqrt N + 16 := by
  obtain ⟨hj, hd⟩ := h
  set s := Nat.sqrt N with hs
  set d := j - s with hdef
  have hjs : j = s + d := by omega
  have hsq : s * s ≤ N := Nat.sqrt_le N
  have h1 : resid N j ≤ 2 * s * d + d * d := by
    have hj2 : j ^ 2 = s * s + (2 * s * d + d * d) := by rw [hjs]; ring
    have : resid N j = s * s + (2 * s * d + d * d) - N := by rw [resid, hj2]
    omega
  have h5 : 5 * d ≤ s + 4 := by omega
  have key : 25 * (2 * s * d + d * d) ≤ 11 * (s * s) + 48 * s + 16 := by nlinarith
  calc 25 * resid N j ≤ 25 * (2 * s * d + d * d) := by exact Nat.mul_le_mul_left _ h1
    _ ≤ 11 * (s * s) + 48 * s + 16 := key
    _ ≤ 11 * N + 48 * s + 16 := by
        have := Nat.mul_le_mul_left 11 hsq
        omega
