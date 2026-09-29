-- Prove2me | solution 1 for Probability.AdaptiveQS.headroom_ratio_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:34:14.479629+00:00
-- url     : https://prove2.me/submissions/91828802-4a10-4c9d-bfb8-6c78728c2107

-- Sol generated from Probability/AdaptiveQSFactorBaseRate.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSFactorBaseRate
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Definitions.Def_Probability_AdaptiveQSTieSlack
import Theorems.Thm_Probability_AdaptiveQS_factorBaseRate_eq_sum_admissible
import Theorems.Thm_Probability_AdaptiveQS_periodRate_nonneg
import Theorems.Thm_Probability_AdaptiveQS_periodRate_pos_of_isSquare
import Theorems.Thm_Probability_AdaptiveQS_sup_periodRate_eq_two_div_min
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The aggregate rate of a quadratic-sieve factor base, and where the headroom lives

`AdaptiveQSResidueRate.lean` computed the per-prime rates exactly: an admissible odd prime
has per-period hit rate `2/p`, an inadmissible one exactly `0`.  Two open directions of the
previous cycle asked what those exact per-prime values say about a whole factor base:

* "Exact Aggregate Period Rate of a Quadratic-Sieve Factor Base" — is the `QR(≤ B)` dial a
  deterministic arithmetic quantity rather than a statistical proxy?
* "Mertens Ceiling on Adaptive Headroom" — the crude bound `oracle_ratio_le_card` says the
  adaptive headroom is at most `|s|`; where does it actually live?

This file settles the algebraic content of both.

* `factorBaseRate` — the aggregate per-period rate of a factor base.
* `factorBaseRate_eq_sum_admissible` — the closed form: the aggregate rate is `Σ 2/p` over
  the admissible primes and depends on the inadmissible ones not at all (the null
  equaliser, aggregated).
* `factorBaseRate_eq_two_mul_harmonic` — hence it is exactly twice the harmonic sum of the
  admissible primes, so the dial is a deterministic function of the factor base.
* `sup_periodRate_eq_two_div_min` — the maximal rate of an admissible factor base is
  attained at its *smallest* prime and equals `2/p_min`: the oracle allocation is
  explicitly identified.
* `headroom_ratio_eq` — the exact oracle-to-mean ratio: `|A| / (p_min · H_A)` where `H_A`
  is the harmonic sum of the admissible primes.  The crude ceiling `|A|` is therefore
  overshooting by exactly the factor `p_min · H_A`, which is the quantity a Mertens
  estimate controls.
* `headroom_ratio_lt_card` — consequently the headroom is *strictly* below the crude
  ceiling as soon as the factor base has more than one prime.
* Lab note `labnote_factorBase_seven_seventeen`: the aggregate rate of the admissible base
  `{7, 17}` for `N = 2` is `2/7 + 2/17`, with the admissibility of both primes decided,
  not assumed.
-/

open Probability.AdaptiveQS

open Finset



/-- **The dial is arithmetic.**  For a fully admissible factor base the aggregate rate is
exactly twice the harmonic sum of its primes: no randomness enters, and the `QR(≤ B)`
counting dial is a deterministic function of the base. -/
theorem factorBaseRate_eq_two_mul_harmonic {N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A) :
    factorBaseRate N A = 2 * ∑ p ∈ A, (1 : ℝ) / p := by
  rw [factorBaseRate_eq_sum_admissible (Finset.Subset.refl A) hA
    (by intro p hp; simp at hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- Every admissible prime has a positive rate, so the aggregate rate of a nonempty
admissible base is positive. -/
theorem factorBaseRate_pos {N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A)
    (hne : A.Nonempty) : 0 < factorBaseRate N A := by
  obtain ⟨q, hq⟩ := hne
  refine Finset.sum_pos' (fun p _ => periodRate_nonneg N p) ⟨q, hq, ?_⟩
  obtain ⟨hprime, hp2, hpN, hpsq⟩ := hA q hq
  haveI : Fact q.Prime := ⟨hprime⟩
  exact periodRate_pos_of_isSquare hp2 hpN hpsq


/-- **Where the headroom lives.**  The ratio of the oracle rate to the mean rate of an
admissible factor base is exactly `|A| / (p_min · H_A)`, with `H_A = Σ_{p ∈ A} 1/p`.  The
crude ceiling `|A|` of `oracle_ratio_le_card` therefore overshoots by precisely the factor
`p_min · H_A`. -/
theorem headroom_ratio_eq {N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A)
    (hne : A.Nonempty) :
    (A.sup' hne (periodRate N)) / (factorBaseRate N A / A.card)
      = (A.card : ℝ) / ((A.min' hne : ℝ) * ∑ p ∈ A, (1 : ℝ) / p) := by
  have hmin := A.min'_mem hne
  obtain ⟨hprime, _, _, _⟩ := hA _ hmin
  have hminpos : (0:ℝ) < (A.min' hne : ℝ) := by exact_mod_cast hprime.pos
  have hHpos : 0 < ∑ p ∈ A, (1 : ℝ) / p := by
    have := factorBaseRate_pos hA hne
    rw [factorBaseRate_eq_two_mul_harmonic hA] at this
    linarith
  rw [sup_periodRate_eq_two_div_min hA hne, factorBaseRate_eq_two_mul_harmonic hA]
  field_simp


/-! ## Lab note — an explicit admissible factor base

For `N = 2` both `7` and `17` are admissible: `2 = 3²` in `ZMod 7` and `2 = 6²` in
`ZMod 17`.  The aggregate per-period rate of the base `{7, 17}` is therefore exactly
`2/7 + 2/17`, and the oracle target is the prime `7`. -/





open Probability.AdaptiveQS in
theorem solution{N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A)
    (hne : A.Nonempty) (hcard : 1 < A.card) :
    (A.sup' hne (periodRate N)) / (factorBaseRate N A / A.card) < A.card := by
  have hmin := A.min'_mem hne
  obtain ⟨hprime, _, _, _⟩ := hA _ hmin
  have hminpos : (0:ℝ) < (A.min' hne : ℝ) := by exact_mod_cast hprime.pos
  -- the harmonic sum exceeds the single term `1 / p_min`
  have hHgt : 1 / (A.min' hne : ℝ) < ∑ p ∈ A, (1 : ℝ) / p := by
    obtain ⟨q, hq, hqne⟩ : ∃ q ∈ A, q ≠ A.min' hne := by
      by_contra hcon
      push_neg at hcon
      have : A ⊆ {A.min' hne} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
      have := Finset.card_le_card this
      simp at this
      omega
    obtain ⟨hqprime, _, _, _⟩ := hA q hq
    have hqpos : (0:ℝ) < (q : ℝ) := by exact_mod_cast hqprime.pos
    have hsub : ({A.min' hne, q} : Finset ℕ) ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hmin
      · rw [Finset.mem_singleton] at hx
        exact hx ▸ hq
    have hpair : ∑ p ∈ ({A.min' hne, q} : Finset ℕ), (1 : ℝ) / p
        = 1 / (A.min' hne : ℝ) + 1 / (q : ℝ) :=
      Finset.sum_pair (Ne.symm hqne)
    have hle : ∑ p ∈ ({A.min' hne, q} : Finset ℕ), (1 : ℝ) / p ≤ ∑ p ∈ A, (1 : ℝ) / p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => ?_
      positivity
    rw [hpair] at hle
    have : 0 < 1 / (q : ℝ) := by positivity
    linarith
  have hminH : 1 < (A.min' hne : ℝ) * ∑ p ∈ A, (1 : ℝ) / p := by
    have hid : (A.min' hne : ℝ) * (1 / (A.min' hne : ℝ)) = 1 := by
      field_simp
    nlinarith [hHgt, hminpos, hid]
  have hcardpos : (0:ℝ) < A.card := by
    have : 0 < A.card := Finset.card_pos.mpr hne
    exact_mod_cast this
  rw [headroom_ratio_eq hA hne]
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [hminH, hcardpos]
