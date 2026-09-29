-- Prove2me | solution 1 for SpikeOrigin.crossingPos_gt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:05:49.696428+00:00
-- url     : https://prove2.me/submissions/70df0316-9e58-49e9-b001-8648688de285

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
theorem solution{N : ℝ} (hhi : N < 2 ^ 96) (hN : 0 < N) :
    (Real.sqrt 6 - 2) / 4 < crossingPos N := by
  have hdiv : (1:ℝ) / 2 < 2 ^ 95 / N := by
    rw [lt_div_iff₀ hN]
    nlinarith
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 / 2 = Real.sqrt (3 / 2) := by
    rw [show (3:ℝ) / 2 = (Real.sqrt 6 / 2) ^ 2 by rw [div_pow, hs6]; norm_num,
      Real.sqrt_sq (by positivity)]
  have hlt : Real.sqrt (3 / 2) < Real.sqrt (1 + 2 ^ 95 / N) := by
    apply Real.sqrt_lt_sqrt (by norm_num); linarith
  unfold crossingPos
  rw [show (Real.sqrt 6 - 2) / 4 = (Real.sqrt 6 / 2 - 1) / 2 by ring, h6]
  linarith
