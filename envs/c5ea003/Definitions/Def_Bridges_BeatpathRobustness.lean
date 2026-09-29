-- Prove2me | Definitions.Def_Bridges_BeatpathRobustness
-- name    : Bridges_BeatpathRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:00.060542+00:00
-- url     : https://prove2.me/theorems/ae02860c-8e77-48a7-8c5b-94e369e689de
-- title:
--   Aether Catalog definitions — Bridges_BeatpathRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BeatpathRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BeatpathRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Satake Beatpath Robustness

This file formalizes a Schulze/beatpath aggregation layer on top of pairwise
tropical Hecke margins for `Fin 3`, and proves a certified robustness theorem
whose radius is governed by the minimum decisive beatpath gap.

## Main Results

* `beatpathStrengthN_lipschitz`: The beatpath closure is 1-Lipschitz with respect
  to uniform perturbations of edge weights.
* `unique_beatpath_winner_stable_of_half_gap`: A unique beatpath winner is preserved
  under perturbations smaller than half the decisive gap.
* `hecke_score_beatpath_stable_under_score_margin_perturbation`: Specialization to
  margins induced by tropical Satake Hecke scores.

## Mathematical Overview

The key mathematical content is that tropical Hecke score geometry induces a weighted
tournament. The Schulze winner is extracted by a max-min path closure, and the closure
is 1-Lipschitz with respect to uniform perturbations of edge weights. This gives a
certified multiclass decision rule distinct from top-2, Condorcet-by-raw-margins,
and score-gap rules.

The 1-Lipschitz property of max-min closure is a structural theorem about the
bottleneck semiring: the operations `min` and `max` are each nonexpansive in the
uniform metric, so any composition of them (including the transitive closure) is
also nonexpansive. This is the conceptual heart of the robustness certificate.
-/


noncomputable section

open Finset

/-! ## Core Definitions -/

/-- A pairwise margin matrix on `Fin n`: `m i j` represents the margin of `i` over `j`. -/
def PairMargin (n : ℕ) := Fin n → Fin n → ℝ

/-- One step of the max-min (widest path) closure on `Fin 3`.
    Updates path strengths by considering all one-hop extensions. -/
def widemaxStep (m p : PairMargin 3) : PairMargin 3 :=
  fun i j => max (p i j)
    (max (min (p i 0) (m 0 j))
      (max (min (p i 1) (m 1 j))
        (min (p i 2) (m 2 j))))

/-- Iterated max-min closure. `beatpathIter m t` gives path strengths using
    paths of length at most `t + 1`. -/
def beatpathIter (m : PairMargin 3) : ℕ → PairMargin 3
  | 0 => m
  | t + 1 => widemaxStep m (beatpathIter m t)

/-- Beatpath strength matrix after `n = 3` iterations of closure.
    On `Fin 3`, this captures all simple paths (length ≤ 2), so it equals
    the true beatpath strength. -/
def beatpathStrengthN (m : PairMargin 3) : PairMargin 3 :=
  beatpathIter m 3

/-- Candidate `c` is a beatpath winner if it strictly dominates every rival
    in beatpath strength. -/
def IsBeatpathWinner (m : PairMargin 3) (c : Fin 3) : Prop :=
  ∀ d, d ≠ c → beatpathStrengthN m c d > beatpathStrengthN m d c

/-- Candidate `c` is the unique beatpath winner. -/
def UniqueBeatpathWinner (m : PairMargin 3) (c : Fin 3) : Prop :=
  IsBeatpathWinner m c ∧ ∀ d, IsBeatpathWinner m d → d = c

/-- Margin matrix induced by a score vector: `scoreMargin H i j = H i - H j`. -/
def scoreMargin (H : Fin 3 → ℝ) : PairMargin 3 :=
  fun i j => H i - H j

/-- Uniform perturbation bound on margin matrices. -/
def MarginPerturbBound (m m' : PairMargin 3) (ε : ℝ) : Prop :=
  ∀ i j, |m' i j - m i j| ≤ ε


/-! ## Helper Lemmas: Lipschitz Properties of min and max -/

/-
`min` is 1-Lipschitz in the uniform metric.
-/

/-
`max` is 1-Lipschitz in the uniform metric.
-/

/-! ## Beatpath Iteration Lipschitz Property -/

/-
The `widemaxStep` operation is 1-Lipschitz: if both the margin matrices
    and the current path matrices are pointwise ε-close, so is the result.
-/

/-
The beatpath iteration is 1-Lipschitz at every step.
-/


/-! ## Winner Uniqueness -/

/-
If `a` strictly dominates `b` in beatpath strength, then `b` cannot be
    a beatpath winner.
-/

/-
A candidate that strictly dominates all rivals in beatpath strength
    is the unique beatpath winner.
-/

/-! ## Gap Degradation and Winner Stability -/

/-
The beatpath gap degrades by at most `2ε` under an `ε`-perturbation.
-/

/-
A beatpath winner is preserved under perturbations smaller than half
    the decisive gap.
-/

/-
A unique beatpath winner is preserved under perturbations smaller than
    half the decisive gap.
-/

/-! ## Hecke Score Specialization -/

/-
If the beatpath gap for a Hecke-score-induced margin is positive,
    the candidate is the unique beatpath winner.
-/

/-
**Robust Schulze certificate for Hecke scores**: if the pairwise margins
    of two score vectors are ε-close and the beatpath gap exceeds 2ε,
    then the beatpath winner is preserved.
-/

/-
**Tropical Satake Schulze certificate**: the full pipeline from
    score perturbation to certified unique beatpath winner.
-/

end


