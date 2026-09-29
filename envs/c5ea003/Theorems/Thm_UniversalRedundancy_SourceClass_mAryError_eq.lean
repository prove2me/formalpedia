-- Prove2me | Theorems.Thm_UniversalRedundancy_SourceClass_mAryError_eq
-- name    : UniversalRedundancy.SourceClass.mAryError_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:55:15.799981+00:00
-- url     : https://prove2.me/theorems/771106a1-4400-47c4-ade1-45d937abfb47
-- title:
--   The error of a rule is one minus its average likelihood score.
-- statement:
--   The error of a rule is one minus its average likelihood score.
--
--   ```lean
--   theorem UniversalRedundancy.SourceClass.mAryError_eq(S : SourceClass X Θ) (T : X → Θ) :
--       S.mAryError T = 1 - (∑ x, S.prob (T x) x) / Fintype.card Θ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/MultiHypothesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/MultiHypothesis.lean#L72

-- Thm stub generated from MachineLearning/TotalVariation/MultiHypothesis.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
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

open UniversalRedundancy

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]

theorem UniversalRedundancy.SourceClass.mAryError_eq(S : SourceClass X Θ) (T : X → Θ) :
    S.mAryError T = 1 - (∑ x, S.prob (T x) x) / Fintype.card Θ := by sorry
