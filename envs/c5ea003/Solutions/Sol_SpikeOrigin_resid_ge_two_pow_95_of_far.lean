-- Prove2me | solution 1 for SpikeOrigin.resid_ge_two_pow_95_of_far
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:12:07.318403+00:00
-- url     : https://prove2.me/submissions/11f6f590-4caa-464b-8102-88fe9fb2c86c

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
theorem solution{N j : ℕ} (hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96)
    (hfar : 142 * Nat.sqrt N ≤ 100 * j) : 2 ^ 95 ≤ resid N j := by
  set s := Nat.sqrt N with hs
  have hup : N < (s + 1) * (s + 1) := by
    have := Nat.lt_succ_sqrt' N
    simpa [hs, pow_two] using this
  have hsle : s ≤ 2 ^ 48 := by
    have : Nat.sqrt N < 2 ^ 48 := Nat.sqrt_lt'.2 (by calc N < 2 ^ 96 := hhi
      _ = (2 ^ 48) ^ 2 := by norm_num)
    omega
  have hexp : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
  have hsq : N ≤ s * s + 2 * s := by omega
  have hj2 : 20164 * (s * s) ≤ 10000 * j ^ 2 := by nlinarith [hfar, sq_nonneg j]
  -- 10000 (j² − N) ≥ 10164 N − 40328 s ≥ 10164·2⁹⁵ − 40328·2⁴⁸ > 10000·2⁹⁵
  have hNj : N ≤ j ^ 2 := by nlinarith
  have hres : 10000 * resid N j = 10000 * j ^ 2 - 10000 * N := by
    rw [resid, Nat.mul_sub]
  have hslack : 40328 * s + 10000 * 2 ^ 95 ≤ 10164 * N := by
    have h1 : 40328 * s ≤ 40328 * 2 ^ 48 := Nat.mul_le_mul_left _ hsle
    have h2 : 40328 * 2 ^ 48 ≤ 164 * 2 ^ 95 := by norm_num
    have h3 : 10164 * 2 ^ 95 ≤ 10164 * N := Nat.mul_le_mul_left _ hlo
    omega
  have : 10000 * 2 ^ 95 ≤ 10000 * resid N j := by
    rw [hres]
    omega
  omega
