-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_factorBaseRate_eq_sum_admissible
-- name    : Probability.AdaptiveQS.factorBaseRate_eq_sum_admissible
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:53:46.187417+00:00
-- url     : https://prove2.me/theorems/5235a962-9f30-40a7-9258-9b10bd047dd1
-- title:
--   The closed form.
-- statement:
--   **The closed form.**  If `A ⊆ FB` collects the admissible primes and every prime of
--   `FB` outside `A` is inadmissible, the aggregate rate is `Σ_{p ∈ A} 2/p` — the inadmissible
--   primes contribute exactly nothing.
--
--   ```lean
--   theorem Probability.AdaptiveQS.factorBaseRate_eq_sum_admissible{N : ℤ} {FB A : Finset ℕ} (hAFB : A ⊆ FB)
--       (hA : AdmissibleFB N A)
--       (hnull : ∀ p ∈ FB \ A, ∃ _ : p.Prime, ¬ IsSquare ((N : ZMod p))) :
--       factorBaseRate N FB = ∑ p ∈ A, 2 / (p : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSFactorBaseRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSFactorBaseRate.lean#L50

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

theorem Probability.AdaptiveQS.factorBaseRate_eq_sum_admissible{N : ℤ} {FB A : Finset ℕ} (hAFB : A ⊆ FB)
    (hA : AdmissibleFB N A)
    (hnull : ∀ p ∈ FB \ A, ∃ _ : p.Prime, ¬ IsSquare ((N : ZMod p))) :
    factorBaseRate N FB = ∑ p ∈ A, 2 / (p : ℝ) := by sorry
