-- Prove2me | solution 1 for SpikeOrigin.resid_lt_of_firstDecile_scalefree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:09:09.631056+00:00
-- url     : https://prove2.me/submissions/d06cd6ad-bd01-47d8-9381-43c1e8d14560

-- Sol generated from Cryptography/SpikeOriginDegeneracy.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
import Theorems.Thm_SpikeOrigin_resid_mul_25_le
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
theorem solution{N j : ℕ} (hN : 2 ^ 16 ≤ N)
    (h : FirstDecile N j) : 100 * resid N j < 45 * N := by
  have h25 := resid_mul_25_le h
  have hs256 : 256 ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt]; norm_num at hN ⊢; omega
  have hsq : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hlin : 256 * Nat.sqrt N ≤ N :=
    le_trans (Nat.mul_le_mul_right _ hs256) hsq
  have hbig : 192 * Nat.sqrt N + 64 < N := by
    have : (65536 : ℕ) ≤ N := by norm_num at hN; omega
    omega
  omega
