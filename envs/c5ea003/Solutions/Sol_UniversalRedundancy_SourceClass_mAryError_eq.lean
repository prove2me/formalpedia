-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.mAryError_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:03:21.164017+00:00
-- url     : https://prove2.me/submissions/d4fa8dbc-b32a-4ced-b888-e8d3fba382c3

-- Sol generated from MachineLearning/TotalVariation/MultiHypothesis.lean
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


omit [Nonempty Θ] in
/-- Regrouping the fibers of a decision rule. -/
lemma sum_fiber_prob (S : SourceClass X Θ) (T : X → Θ) :
    ∑ θ, ∑ x ∈ univ.filter fun x => T x = θ, S.prob θ x = ∑ x, S.prob (T x) x := by
  classical
  have h1 : ∀ θ : Θ, ∑ x ∈ univ.filter fun x => T x = θ, S.prob θ x
      = ∑ x, if T x = θ then S.prob θ x else 0 := fun θ => Finset.sum_filter _ _
  rw [Finset.sum_congr rfl fun θ _ => h1 θ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq univ (T x) fun θ => S.prob θ x]
  simp










open UniversalRedundancy in
theorem solution(S : SourceClass X Θ) (T : X → Θ) :
    S.mAryError T = 1 - (∑ x, S.prob (T x) x) / Fintype.card Θ := by
  classical
  have hm : (Fintype.card Θ : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := Θ)
    positivity
  have hrow : ∀ θ : Θ, ∑ x ∈ univ.filter (fun x => T x ≠ θ), S.prob θ x
      = 1 - ∑ x ∈ univ.filter (fun x => T x = θ), S.prob θ x := by
    intro θ
    have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun x => T x = θ) (S.prob θ)
    rw [S.sum_one θ] at hsplit
    have hfil : (univ.filter fun x => T x ≠ θ) = univ.filter fun x => ¬ (T x = θ) := by
      simp [ne_eq]
    rw [hfil]
    linarith
  rw [mAryError, Finset.sum_congr rfl fun θ _ => hrow θ, Finset.sum_sub_distrib,
    sum_fiber_prob, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp
