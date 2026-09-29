-- Prove2me | Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
-- name    : MachineLearning_TotalVariation_MultiHypothesis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:30.842566+00:00
-- url     : https://prove2.me/theorems/1db83b3c-6f4c-4d1c-9238-0d2e2bf0c945
-- title:
--   Aether Catalog definitions — MachineLearning_TotalVariation_MultiHypothesis
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TotalVariation.MultiHypothesis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TotalVariation/MultiHypothesis.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Shtarkov sum *is* the multi-hypothesis testing optimum

`Testing` identified the binary optimum: the least average error of a Boolean
test for `p` versus `q` is `(1 − d_TV(p, q))/2`.  The catalog's universal-coding
thread knows a different quantity for the same pair — the **Shtarkov sum**
`Cₛ = ∑ₓ max_θ p_θ x`, with `Cₛ = 1 + d_TV(p, q)` for two sources.

Those two facts are not a coincidence.  This file proves the general identity:
for a class of `m` sources under a uniform prior, the least average error of an
`m`-ary decision rule is

`1 − Cₛ / m`,

attained by the maximum-likelihood rule.  The universal-coding price and the
statistical testing optimum are literally the same sum, viewed twice.  The
binary case reproduces `isLeast_bayesError` on the nose
(`isLeast_mAryError_bool`), which is a nontrivial cross-check of the two
independent developments.

Two rigidity corollaries come for free from the catalog's endpoint analysis:

* mutually singular sources give error `0` (perfect identification);
* identical sources give error `1 − 1/m` (pure guessing);
* and quantitatively, sources within `ε` of a common reference force error at
  least `(m − 1)/m − ε` (`mAryError_ge_of_tvDist`), the multi-hypothesis Le Cam
  bound.

## Main results

* `SourceClass.mAryError`, `SourceClass.mAryError_eq` — the error functional;
* `SourceClass.isLeast_mAryError` — the optimum is `1 − Cₛ/m`;
* `SourceClass.isLeast_mAryError_bool` — binary consistency with `Testing`;
* `SourceClass.mAryError_ge_of_tvDist` — the multi-hypothesis Le Cam bound;
* `SourceClass.mAryError_eq_zero_iff_mutuallySingular` — the rigid endpoint.

## Application keywords

multi-hypothesis testing, Bayes risk, maximum likelihood, Shtarkov sum,
universal coding, Le Cam method
-/


open Finset

namespace UniversalRedundancy

namespace SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]

/-- Average (uniform-prior) error probability of the `m`-ary decision rule `T`,
which reads the sample `x` and outputs the hypothesis `T x`. -/
noncomputable def mAryError (S : SourceClass X Θ) (T : X → Θ) : ℝ :=
  (∑ θ, ∑ x ∈ univ.filter fun x => T x ≠ θ, S.prob θ x) / Fintype.card Θ



/-- The maximum-likelihood decision rule. -/
noncomputable def mlRule (S : SourceClass X Θ) (x : X) : Θ :=
  (Finite.exists_max fun θ => S.prob θ x).choose






end SourceClass

end UniversalRedundancy


