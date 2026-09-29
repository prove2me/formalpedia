-- Prove2me | solution 1 for CollatzSpectral.resonance_sets_pairwise_distinct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:19:26.846828+00:00
-- url     : https://prove2.me/submissions/d7c52676-4840-4ae4-a893-b62b7df338c7

-- Sol generated from Novelty/CollatzSpectralResonance.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized
import Theorems.Thm_CollatzSpectral_limitAmp_eq_zero_iff
import Theorems.Thm_CollatzSpectral_no_resonance_five_one_fifth
import Theorems.Thm_CollatzSpectral_no_resonance_seven_one_fifth
import Theorems.Thm_CollatzSpectral_resonance_three_one_fifth

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










open CollatzSpectral in
theorem solution:
    (limitAmp 3 (1 / 5 : ℝ) = 0 ∧ limitAmp 5 (1 / 5 : ℝ) ≠ 0 ∧ limitAmp 7 (1 / 5 : ℝ) ≠ 0) ∧
    (limitAmp 5 (1 / 9 : ℝ) = 0 ∧ limitAmp 3 (1 / 9 : ℝ) ≠ 0 ∧ limitAmp 7 (1 / 9 : ℝ) ≠ 0) ∧
    (limitAmp 7 (1 / 13 : ℝ) = 0 ∧ limitAmp 3 (1 / 13 : ℝ) ≠ 0 ∧
      limitAmp 5 (1 / 13 : ℝ) ≠ 0) := by
  refine ⟨⟨resonance_three_one_fifth, no_resonance_five_one_fifth,
      no_resonance_seven_one_fifth⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [limitAmp_eq_zero_iff]; exact ⟨0, by norm_num⟩
  · rw [Ne, limitAmp_eq_zero_iff]
    rintro ⟨m, hm⟩
    norm_num at hm
    have hz : (5 : ℤ) = 18 * m + 9 := by exact_mod_cast (by linarith : (5 : ℝ) = 18 * m + 9)
    omega
  · rw [Ne, limitAmp_eq_zero_iff]
    rintro ⟨m, hm⟩
    norm_num at hm
    have hz : (13 : ℤ) = 18 * m + 9 := by exact_mod_cast (by linarith : (13 : ℝ) = 18 * m + 9)
    omega
  · rw [limitAmp_eq_zero_iff]; exact ⟨0, by norm_num⟩
  · rw [Ne, limitAmp_eq_zero_iff]
    rintro ⟨m, hm⟩
    norm_num at hm
    have hz : (5 : ℤ) = 26 * m + 13 := by exact_mod_cast (by linarith : (5 : ℝ) = 26 * m + 13)
    omega
  · rw [Ne, limitAmp_eq_zero_iff]
    rintro ⟨m, hm⟩
    norm_num at hm
    have hz : (9 : ℤ) = 26 * m + 13 := by exact_mod_cast (by linarith : (9 : ℝ) = 26 * m + 13)
    omega
