-- Prove2me | solution 1 for CertifiedEvidence.periodic_ext
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:42:58.053762+00:00
-- url     : https://prove2.me/submissions/a402b87f-3471-4ac6-a599-d03834fa3197

-- Sol generated from MachineLearning/CertifiedEvidence/LearningBoundary.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Insufficiency
import Definitions.Def_MachineLearning_CertifiedEvidence_LearningBoundary
import Definitions.Def_MachineLearning_CertifiedEvidence_Sufficiency
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Where the boundary of finite evidence actually lies

`CertifiedEvidence.Insufficiency` shows the version space after finite evidence
has the cardinality of the continuum — but that is a statement about the
*unrestricted* hypothesis class `ℕ → Bool`.  This file proves the matching
positive statement: restrict the class and the very same evidence becomes
conclusive, with an exactly determined sample complexity.

## Main results

* `periodic_ext` — two `T`-periodic predicates that agree on `[1,T]` agree
  everywhere above `0`.
* `periodic_versionSpace_subsingleton` — inside the class of `T`-periodic
  predicates, the version space after the `T` samples `1,…,T` is a singleton:
  finite evidence *does* identify the hypothesis.
* `periodic_sample_complexity_sharp` — and `T` samples are necessary: for every
  `T ≥ 2` two distinct `T`-periodic predicates agree on `[1,T-1]`.
* `learning_dichotomy` — the two regimes side by side: continuum-sized version
  space for the unrestricted class, singleton for the periodic class, at the
  same sample size.
* `certifiable_iff_descent` — the computational counterpart, transported from
  `CertifiedEvidence.Sufficiency`: a universal statement is provable from a
  finite window precisely when a descent structure exists.
-/


open CertifiedEvidence









open CertifiedEvidence in
theorem solution{T : ℕ} (hT : 0 < T) {p q : ℕ → Bool}
    (hp : p ∈ PeriodicClass T) (hq : q ∈ PeriodicClass T)
    (hagree : ∀ k, 1 ≤ k → k ≤ T → p k = q k) :
    ∀ n, 1 ≤ n → p n = q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      by_cases h : n ≤ T
      · exact hagree n hn h
      · push_neg at h
        have hback : n - T + T = n := by omega
        have h1 : p n = p (n - T) := by
          have hpp := hp (n - T); rwa [hback] at hpp
        have h2 : q n = q (n - T) := by
          have hqq := hq (n - T); rwa [hback] at hqq
        rw [h1, h2]
        exact ih (n - T) (by omega) (by omega)
