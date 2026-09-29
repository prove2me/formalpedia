-- Prove2me | solution 1 for CollatzSpectral.common_resonance_three_five
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:13:44.618803+00:00
-- url     : https://prove2.me/submissions/d07f54bb-5ddd-43d3-acd0-a9f481e4adcc

-- Sol generated from Novelty/CollatzSpectralResonance.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized
import Theorems.Thm_CollatzSpectral_limitAmp_eq_zero_iff

/-!
# The arithmetic of the resonance sets of the `a n + 1` maps

`Catalog/Novelty/CollatzSpectralNormalized.lean` shows that the normalized
transform of the `a n + 1` map converges to `limitAmp a ω`, and that it vanishes
exactly on the *resonance set*

`R a = {ω : (2a - 1) ω ∈ 2ℤ + 1}`.

This file studies the arithmetic of these sets.  The picture that emerges is a
clean dichotomy:

* every multiplier resonates at every odd integer frequency
  (`limitAmp_odd_int`) — these carry no information about `a`;
* off the odd integers the resonance sets are genuinely different, and their
  pairwise intersections are governed by a linear Diophantine condition.  For
  the three classical multipliers we compute the intersections exactly
  (`common_resonance_three_five`, `common_resonance_three_seven`,
  `common_resonance_five_seven`): they contain *nothing but* the trivial odd
  integers.

Thus any spectral discriminator between the `3n+1`, `5n+1` and `7n+1` maps must
be read off at non-integer frequencies; the behaviour near frequency `0`, or at
any integer frequency, is identical for all three maps
(`limitAmp_int_indep_of_multiplier`).
-/

open CollatzSpectral

open Filter Complex
open scoped Real Topology

/-- Every multiplier resonates at every odd integer frequency. -/
theorem limitAmp_odd_int (a : ℕ) (t : ℤ) : limitAmp a (2 * (t : ℝ) + 1) = 0 := by
  rw [limitAmp_eq_zero_iff]
  refine ⟨(2 * (a : ℤ) - 1) * t + ((a : ℤ) - 1), ?_⟩
  push_cast
  ring



/-- A convenient reformulation of the resonance condition for two multipliers. -/
lemma resonance_pair_diophantine (a b : ℕ) (ω : ℝ)
    (ha : ∃ m : ℤ, (2 * (a : ℝ) - 1) * ω = 2 * m + 1)
    (hb : ∃ k : ℤ, (2 * (b : ℝ) - 1) * ω = 2 * k + 1) :
    ∃ m k : ℤ, (2 * (b : ℤ) - 1) * (2 * m + 1) = (2 * (a : ℤ) - 1) * (2 * k + 1) ∧
      (2 * (a : ℝ) - 1) * ω = 2 * m + 1 := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨k, hk⟩ := hb
  refine ⟨m, k, ?_, hm⟩
  have hR : (2 * (b : ℝ) - 1) * (2 * (m : ℝ) + 1) = (2 * (a : ℝ) - 1) * (2 * (k : ℝ) + 1) := by
    rw [← hm, ← hk]
    ring
  exact_mod_cast hR






open CollatzSpectral in
theorem solution(ω : ℝ) :
    (limitAmp 3 ω = 0 ∧ limitAmp 5 ω = 0) ↔ ∃ t : ℤ, ω = 2 * (t : ℝ) + 1 := by
  constructor
  · rintro ⟨h3, h5⟩
    obtain ⟨m, k, hzz, hm⟩ := resonance_pair_diophantine 3 5 ω
      ((limitAmp_eq_zero_iff 3 ω).mp h3) ((limitAmp_eq_zero_iff 5 ω).mp h5)
    push_cast at hzz hm
    refine ⟨(m - 2) / 5, ?_⟩
    have hint : 2 * m + 1 = 5 * (2 * ((m - 2) / 5) + 1) := by omega
    have hR : 2 * (m : ℝ) + 1 = 5 * (2 * (((m - 2) / 5 : ℤ) : ℝ) + 1) := by exact_mod_cast hint
    linarith
  · rintro ⟨t, rfl⟩
    exact ⟨limitAmp_odd_int 3 t, limitAmp_odd_int 5 t⟩
