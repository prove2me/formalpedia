-- Prove2me | Theorems.Thm_UniversalRedundancy_SourceClass_mAryError_ge_of_tvDist
-- name    : UniversalRedundancy.SourceClass.mAryError_ge_of_tvDist
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:55:57.597032+00:00
-- url     : https://prove2.me/theorems/0cd27f23-24f1-4674-90c4-0cebc7443fed
-- title:
--   Multi-hypothesis Le Cam bound.
-- statement:
--   **Multi-hypothesis Le Cam bound.**  If every source is within `ε` of a
--   common reference `θ₀` in total variation, then *no* decision rule can beat
--   `(m − 1)/m − ε`: an `m`-way statistical problem is essentially unsolvable when
--   the hypotheses cluster.
--
--   ```lean
--   theorem UniversalRedundancy.SourceClass.mAryError_ge_of_tvDist(S : SourceClass X Θ) (θ₀ : Θ) {ε : ℝ}
--       (hε : ∀ θ, tvDist (S.prob θ) (S.prob θ₀) ≤ ε / Fintype.card Θ) (T : X → Θ) :
--       1 - 1 / Fintype.card Θ - ε / Fintype.card Θ ≤ S.mAryError T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/MultiHypothesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/MultiHypothesis.lean#L135

-- Thm stub generated from MachineLearning/TotalVariation/MultiHypothesis.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
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

open UniversalRedundancy

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]

theorem UniversalRedundancy.SourceClass.mAryError_ge_of_tvDist(S : SourceClass X Θ) (θ₀ : Θ) {ε : ℝ}
    (hε : ∀ θ, tvDist (S.prob θ) (S.prob θ₀) ≤ ε / Fintype.card Θ) (T : X → Θ) :
    1 - 1 / Fintype.card Θ - ε / Fintype.card Θ ≤ S.mAryError T := by sorry
