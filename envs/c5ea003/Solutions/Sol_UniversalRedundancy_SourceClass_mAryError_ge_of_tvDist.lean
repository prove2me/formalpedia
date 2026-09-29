-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.mAryError_ge_of_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:12:00.011622+00:00
-- url     : https://prove2.me/submissions/10815d34-8790-4873-8cd3-aa204d3b3a57

-- Sol generated from MachineLearning/TotalVariation/MultiHypothesis.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_MultiHypothesis
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_SourceClass_isLeast_mAryError
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_le_one_add_sum_tvDist
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
theorem solution(S : SourceClass X Θ) (θ₀ : Θ) {ε : ℝ}
    (hε : ∀ θ, tvDist (S.prob θ) (S.prob θ₀) ≤ ε / Fintype.card Θ) (T : X → Θ) :
    1 - 1 / Fintype.card Θ - ε / Fintype.card Θ ≤ S.mAryError T := by
  have hmpos : (0:ℝ) < Fintype.card Θ := by
    have := Fintype.card_pos (α := Θ)
    positivity
  have hub : S.shtarkovSum ≤ 1 + ε := by
    have h1 := shtarkovSum_le_one_add_sum_tvDist S θ₀
    have h2 : ∑ θ, tvDist (S.prob θ) (S.prob θ₀) ≤ ∑ _θ : Θ, ε / Fintype.card Θ :=
      Finset.sum_le_sum fun θ _ => hε θ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have h3 : (Fintype.card Θ : ℝ) * (ε / Fintype.card Θ) = ε := by
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  have hlow := (isLeast_mAryError S).2 ⟨T, rfl⟩
  have hdiv : S.shtarkovSum / Fintype.card Θ ≤ (1 + ε) / Fintype.card Θ :=
    (div_le_div_iff_of_pos_right hmpos).mpr hub
  have hsplit : (1 + ε) / (Fintype.card Θ : ℝ)
      = 1 / Fintype.card Θ + ε / Fintype.card Θ := by ring
  linarith [hlow, hdiv, hsplit.le, hsplit.ge]
