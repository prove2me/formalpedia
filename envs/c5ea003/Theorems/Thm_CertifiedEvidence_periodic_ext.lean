-- Prove2me | Theorems.Thm_CertifiedEvidence_periodic_ext
-- name    : CertifiedEvidence.periodic_ext
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:10.132113+00:00
-- url     : https://prove2.me/theorems/cacf49fa-68d4-49d5-a14f-549ec30caee0
-- title:
--   A `T`-periodic predicate is determined above `0` by its values on `[1,T]`.
-- statement:
--   A `T`-periodic predicate is determined above `0` by its values on `[1,T]`.
--
--   ```lean
--   theorem CertifiedEvidence.periodic_ext{T : ℕ} (hT : 0 < T) {p q : ℕ → Bool}
--       (hp : p ∈ PeriodicClass T) (hq : q ∈ PeriodicClass T)
--       (hagree : ∀ k, 1 ≤ k → k ≤ T → p k = q k) :
--       ∀ n, 1 ≤ n → p n = q n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/LearningBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/LearningBoundary.lean#L38

-- Thm stub generated from MachineLearning/CertifiedEvidence/LearningBoundary.lean
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

theorem CertifiedEvidence.periodic_ext{T : ℕ} (hT : 0 < T) {p q : ℕ → Bool}
    (hp : p ∈ PeriodicClass T) (hq : q ∈ PeriodicClass T)
    (hagree : ∀ k, 1 ≤ k → k ≤ T → p k = q k) :
    ∀ n, 1 ≤ n → p n = q n := by sorry
