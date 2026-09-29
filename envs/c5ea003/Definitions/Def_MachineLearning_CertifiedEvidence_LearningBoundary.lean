-- Prove2me | Definitions.Def_MachineLearning_CertifiedEvidence_LearningBoundary
-- name    : MachineLearning_CertifiedEvidence_LearningBoundary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:27.200605+00:00
-- url     : https://prove2.me/theorems/b8f63ac9-3277-405f-9dc7-1315e7b30a6f
-- title:
--   Aether Catalog definitions — MachineLearning_CertifiedEvidence_LearningBoundary
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CertifiedEvidence.LearningBoundary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CertifiedEvidence/LearningBoundary.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Insufficiency
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


namespace CertifiedEvidence

/-- The hypothesis class of predicates with period `T`. -/
def PeriodicClass (T : ℕ) : Set (ℕ → Bool) := {p | ∀ n, p (n + T) = p n}







end CertifiedEvidence


