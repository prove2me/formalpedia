-- Prove2me | solution 1 for Probability.AdaptiveQS.sup_periodRate_eq_two_div_min
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:57.85333+00:00
-- url     : https://prove2.me/submissions/ab3cebbc-7d0c-4723-ad16-6c5d400fb765

-- Sol generated from Probability/AdaptiveQSFactorBaseRate.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSFactorBaseRate
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Definitions.Def_Probability_AdaptiveQSTieSlack
import Theorems.Thm_Probability_AdaptiveQS_periodRate_eq_two_div
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








/-! ## Lab note — an explicit admissible factor base

For `N = 2` both `7` and `17` are admissible: `2 = 3²` in `ZMod 7` and `2 = 6²` in
`ZMod 17`.  The aggregate per-period rate of the base `{7, 17}` is therefore exactly
`2/7 + 2/17`, and the oracle target is the prime `7`. -/





open Probability.AdaptiveQS in
theorem solution{N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A)
    (hne : A.Nonempty) :
    A.sup' hne (periodRate N) = 2 / (A.min' hne : ℝ) := by
  have hmin := A.min'_mem hne
  obtain ⟨hprime, hp2, hpN, hpsq⟩ := hA _ hmin
  haveI : Fact (A.min' hne).Prime := ⟨hprime⟩
  have hminrate : periodRate N (A.min' hne) = 2 / (A.min' hne : ℝ) :=
    periodRate_eq_two_div hp2 hpN hpsq
  refine le_antisymm (Finset.sup'_le _ _ fun p hp => ?_) (hminrate ▸ Finset.le_sup' _ hmin)
  obtain ⟨hqprime, hq2, hqN, hqsq⟩ := hA p hp
  haveI : Fact p.Prime := ⟨hqprime⟩
  rw [periodRate_eq_two_div hq2 hqN hqsq]
  have hle : (A.min' hne : ℝ) ≤ (p : ℝ) := by exact_mod_cast A.min'_le p hp
  have hpos : (0:ℝ) < (A.min' hne : ℝ) := by exact_mod_cast hprime.pos
  exact div_le_div_of_nonneg_left (by norm_num) hpos hle
