-- Prove2me | Definitions.Def_Bridges_TropicalTopKRobustnessGL3
-- name    : Bridges_TropicalTopKRobustnessGL3
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:03.089684+00:00
-- url     : https://prove2.me/theorems/4f03fa8d-7c93-4a04-9447-f51c5186271c
-- title:
--   Aether Catalog definitions — Bridges_TropicalTopKRobustnessGL3
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalTopKRobustnessGL3`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalTopKRobustnessGL3.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Satake Top-K Robustness for GL₃ Hecke Score Classifiers

This file upgrades the tropical Satake margin robustness story from top-1 argmax
stability to top-k ranking stability for finitely many GL₃ Hecke-score classes.

## Main results

- `separated_order_preserved_of_uniform_score_close`: pairwise order preservation under
  uniform perturbation — the engine of the whole argument.
- `topKSet_eq_of_uniform_score_close`: the full abstract top-k invariance theorem under
  uniform score perturbation with gap condition.
- `topKSet_eq_of_lipschitz_gap`: metric/Lipschitz version of top-k invariance.
- `argmax_stable_of_topK_gap`: the k=1 specialization recovering the argmax theorem.
- `tropical_GL3_topK_certified_robust`: GL₃ tropical certificate form.

## Overview

The core mathematical insight is that if the k-th and (k+1)-th ranked scores are
separated by a gap Δ, and all scores are perturbed by at most η with 2η < Δ,
then the top-k set is invariant. This extends the classical argmax robustness theorem
(k=1) to set-valued decisions used in shortlist decoding, beam search, multiclass
retrieval, and ranking-based certified robustness.

The definition of `topKSet` is tie-tolerant: it includes all labels with fewer than k
labels strictly above them. When there are no ties at the k-th boundary (ensured by the
exact cardinality condition `(topKSet score k).card = k`), the gap condition between the
k-th and (k+1)-th ranked labels guarantees exact preservation of the top-k set under
perturbation.
-/

noncomputable section

open scoped BigOperators

/-! ### Core definitions -/

variable {ι : Type*}

/-- The top-k label set: labels `i` such that fewer than `k` labels strictly outscore `i`.
This definition is tie-tolerant in the right way for robustness statements. -/
def topKSet [Fintype ι] [DecidableEq ι] (score : ι → ℝ) (k : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => (Finset.univ.filter fun j => score i < score j).card < k)

/-- The score-gap predicate: there is a positive gap Δ between every selected and every
unselected label. -/
def topKGapAt [Fintype ι] [DecidableEq ι] (score : ι → ℝ) (k : ℕ) (Δ : ℝ) : Prop :=
  0 < Δ ∧
  ∀ ⦃i j : ι⦄, i ∈ topKSet score k → j ∉ topKSet score k → Δ ≤ score i - score j

/-- Uniform perturbation bound: every score changes by at most η. -/
def UniformScoreClose (score score' : ι → ℝ) (η : ℝ) : Prop :=
  ∀ i, |score' i - score i| ≤ η

/-- A score family indexed by a space α is K-Lipschitz with respect to a distance d. -/
def IsKLipschitzFamily {α : Type*} (d : α → α → ℝ) (score : α → ι → ℝ) (K : ℝ) : Prop :=
  ∀ x y i, |score x i - score y i| ≤ K * d x y

/-- The boundary-gap predicate (equivalent formulation). -/
def topKBoundaryGapAt [Fintype ι] [DecidableEq ι] (score : ι → ℝ) (k : ℕ) (Δ : ℝ) : Prop :=
  0 < Δ ∧
  ∀ ⦃i j : ι⦄,
    i ∈ topKSet score k →
    j ∉ topKSet score k →
    score j ≤ score i - Δ

/-! ### Characterization lemmas -/

variable [Fintype ι] [DecidableEq ι]



/-! ### Pairwise perturbation lemma -/


/-! ### Top-k subset inclusions -/


/-
The set of labels that beat `i` in the perturbed scores is contained in the
original top-k set (minus `i` itself). Key step for the cardinality argument.
-/

/-
**Forward inclusion**: every label in the original top-k set remains in the
perturbed top-k set, provided the original top-k set has exactly k elements
(no ties at the k-th boundary).
-/

/-
**Reverse inclusion**: every element of the top-k set of a perturbed score
is in the top-k set of the original score, given a gap condition.
-/


/-! ### Metric/Lipschitz version -/



/-! ### Top-1 specialization: argmax stability -/


/-! ### Pointwise membership form -/


/-! ### GL₃ Tropical Certificate Form -/


end


