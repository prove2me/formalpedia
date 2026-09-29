-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.mAryError_eq_zero_iff_mutuallySingular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:09:03.466158+00:00
-- url     : https://prove2.me/submissions/51fafcfb-438f-49b9-91c5-9db8cf6cedb7

-- Sol generated from MachineLearning/TotalVariation/MultiHypothesis.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_eq_card_iff_mutuallySingular
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












open UniversalRedundancy in
omit [DecidableEq Θ] in
theorem solution(S : SourceClass X Θ) :
    (1 - S.shtarkovSum / Fintype.card Θ) = 0 ↔ S.MutuallySingular := by
  have hmpos : (0:ℝ) < Fintype.card Θ := by
    have := Fintype.card_pos (α := Θ)
    positivity
  rw [← shtarkovSum_eq_card_iff_mutuallySingular]
  constructor
  · intro h
    have : S.shtarkovSum / Fintype.card Θ = 1 := by linarith
    field_simp at this
    exact this
  · intro h
    rw [h, div_self (ne_of_gt hmpos)]
    ring
