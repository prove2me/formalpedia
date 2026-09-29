-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_headroom_ratio_lt_card
-- name    : Probability.AdaptiveQS.headroom_ratio_lt_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:54:53.971527+00:00
-- url     : https://prove2.me/theorems/b369672e-a2b0-4f4e-bc31-759d40f78419
-- title:
--   The crude ceiling is never attained by a real factor base.
-- statement:
--   **The crude ceiling is never attained by a real factor base.**  As soon as the
--   admissible base contains two primes, `p_min · H_A > 1`, so the headroom ratio is strictly
--   below the number of primes: adaptive gains cannot scale with the size of the factor
--   base.
--
--   ```lean
--   theorem Probability.AdaptiveQS.headroom_ratio_lt_card{N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A)
--       (hne : A.Nonempty) (hcard : 1 < A.card) :
--       (A.sup' hne (periodRate N)) / (factorBaseRate N A / A.card) < A.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSFactorBaseRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSFactorBaseRate.lean#L126

-- Thm stub generated from Probability/AdaptiveQSFactorBaseRate.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSFactorBaseRate
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Definitions.Def_Probability_AdaptiveQSTieSlack
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

theorem Probability.AdaptiveQS.headroom_ratio_lt_card{N : ℤ} {A : Finset ℕ} (hA : AdmissibleFB N A)
    (hne : A.Nonempty) (hcard : 1 < A.card) :
    (A.sup' hne (periodRate N)) / (factorBaseRate N A / A.card) < A.card := by sorry
