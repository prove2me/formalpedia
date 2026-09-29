-- Prove2me | solution 1 for SpikeOrigin.exclusion_phase_transition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:07:39.976802+00:00
-- url     : https://prove2.me/submissions/0f6aedb1-c123-4bf4-a6cd-8519d3621b9e

-- Sol generated from Cryptography/SpikeOriginDegeneracy.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
import Theorems.Thm_SpikeOrigin_crossingPos_gt
import Theorems.Thm_SpikeOrigin_crossingPos_spec
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



/-- Upper end of the crossing interval: for `N ≥ 2⁹⁵`, `u₀(N) ≤ (√2 − 1)/2 ≈ 0.20711`. -/
theorem crossingPos_le {N : ℝ} (hlo : (2:ℝ) ^ 95 ≤ N) :
    crossingPos N ≤ (Real.sqrt 2 - 1) / 2 := by
  have hN : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hlo
  have hdiv : (2:ℝ) ^ 95 / N ≤ 1 := (div_le_one hN).2 hlo
  have : Real.sqrt (1 + 2 ^ 95 / N) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  unfold crossingPos; linarith





open SpikeOrigin in
theorem solution{c : ℝ} :
    (c ≤ (Real.sqrt 6 - 2) / 4 →
      ∀ N u : ℝ, 0 < N → N < 2 ^ 96 → 0 ≤ u → u < c →
        ((1 + 2 * u) ^ 2 - 1) * N < 2 ^ 95) ∧
    ((Real.sqrt 2 - 1) / 2 < c →
      ∀ N : ℝ, (2:ℝ) ^ 95 ≤ N → ∃ u : ℝ, 0 ≤ u ∧ u < c ∧ 2 ^ 95 ≤ ((1 + 2 * u) ^ 2 - 1) * N) := by
  constructor
  · intro hc N u hN hhi hu hlt
    by_contra hcon
    push_neg at hcon
    have := (crossingPos_spec hN hu).1 hcon
    have := crossingPos_gt hhi hN
    linarith
  · intro hc N hlo
    have hN : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hlo
    refine ⟨(Real.sqrt 2 - 1) / 2, ?_, hc, ?_⟩
    · have : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    · exact (crossingPos_spec hN (by
        have : (1:ℝ) ≤ Real.sqrt 2 := by
          rw [show (1:ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_le_sqrt (by norm_num)
        linarith)).2 (crossingPos_le hlo)
