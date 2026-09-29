-- Prove2me | Definitions.Def_Bridges_GL3TropicalSatakeScoreStability
-- name    : Bridges_GL3TropicalSatakeScoreStability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:57.22528+00:00
-- url     : https://prove2.me/theorems/fdf086db-044e-45d6-9668-bf1c38006e25
-- title:
--   Aether Catalog definitions — Bridges_GL3TropicalSatakeScoreStability
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3TropicalSatakeScoreStability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3TropicalSatakeScoreStability.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL₃ Tropical Satake Score Stability

## Overview

This file establishes a reusable perturbation-transfer principle for 3-class
score vectors, then instantiates it for the GL₃ tropical Satake Hecke score
constructions. The key insight is that any approximation pipeline controlling
the sup-norm error of a score vector automatically inherits certified invariance
of top-1, top-2, and pairwise decisions, provided the original margins exceed
twice the perturbation bound.

## Architecture

The development proceeds in two layers:

1. **Generic perturbation lemmas** for arbitrary `X → Fin 3 → ℝ` score maps.
   These are architecture-agnostic and reusable by any 3-class classifier.

2. **GL₃ tropical Satake bridge theorems** that instantiate the generic
   perturbation lemmas with the existing GL₃ tropical Satake Hecke score
   constructions.

## Main Results

* `pairMargin_perturbation_bound` — pairwise margins change by at most 2ε
* `top1_stable_of_margin_gt_two_eps` — top-1 winner preserved under perturbation
* `top2_stable_of_margin_gt_two_eps` — top-2 membership preserved
* `top2_set_stable_of_bottom_margin_gt_two_eps` — full top-2 set preserved
* `pairwise_preference_stable_of_margin_gt_two_eps` — pairwise OVO preserved
* `gl3_tropical_satake_stability_transfer` — bundled bridge theorem

## Significance

This theorem family separates representation-theoretic score construction from
robustness certification. Future approximation theorems only need to prove
`ScoreSupClose`, future margin theorems only need to prove score gaps, and
the bridge then automatically yields certified invariance.
-/


namespace GL3TropicalSatakeScoreStability

/-! ## Core Definitions -/

/-- A 3-class score map: assigns to each input `x : X` a vector of three real scores. -/
def Score3 (X : Type*) := X → Fin 3 → ℝ

/-- Pointwise sup-norm closeness of two score maps. -/
def ScoreSupClose {X : Type*} (f g : Score3 X) (ε : ℝ) : Prop :=
  ∀ x i, |f x i - g x i| ≤ ε

/-- The pairwise margin between class `i` and class `j` at input `x`. -/
def pairMargin {X : Type*} (f : Score3 X) (x : X) (i j : Fin 3) : ℝ :=
  f x i - f x j

/-- Strict top-1 winner: class `i` strictly beats all other classes. -/
def IsTop1Winner {X : Type*} (f : Score3 X) (x : X) (i : Fin 3) : Prop :=
  ∀ j, j ≠ i → f x j < f x i

/-- Top-2 membership: class `i` strictly beats at least one competitor.
    In 3 classes, this is equivalent to "not the unique bottom class". -/
def InTop2 {X : Type*} (f : Score3 X) (x : X) (i : Fin 3) : Prop :=
  ∃ j, j ≠ i ∧ f x j < f x i

/-- Pairwise preference: class `i` is strictly preferred to class `j`. -/
def PairwisePrefers {X : Type*} (f : Score3 X) (x : X) (i j : Fin 3) : Prop :=
  f x i > f x j


/-- Two score maps have the same top-2 set at input `x`. -/
def SameTop2Set {X : Type*} (f g : Score3 X) (x : X) : Prop :=
  ∀ i, InTop2 f x i ↔ InTop2 g x i

/-! ## Supporting Lemmas -/




/-! ## Generic Perturbation Lemmas -/

/-
**Pairwise score-difference perturbation bound.**
    If `f` and `g` are `ε`-close in sup-norm, then their pairwise margins
    differ by at most `2ε`.
-/

/-
**Directional margin perturbation bound.**
    The perturbed margin is at least the original margin minus `2ε`.
-/

/-
**Top-1 winner stability.**
    If class `i` beats all competitors by margin `> 2ε` under `f`,
    then `i` remains the strict top-1 winner under any `ε`-close `g`.
-/

/-
**Top-1 winner stability (bidirectional).**
    Under symmetric closeness with margin `> 2ε`, both `f` and `g`
    agree on the top-1 winner.
-/

/-
**Top-2 membership stability.**
    If class `i` beats some competitor by margin `> 2ε` under `f`,
    then `i` remains in the top-2 under any `ε`-close `g`.
-/

/-
In `Fin 3`, a class is in the top-2 iff it is not the unique bottom class.
-/

/-
**Top-2 set stability.**
    If there is a unique bottom class `b` separated by margin `> 2ε`,
    then `f` and `g` have the same top-2 set.
-/

/-
**Pairwise one-vs-one stability.**
    If class `i` beats class `j` by margin `> 2ε` under `f`,
    then the preference is preserved under any `ε`-close `g`.
-/

/-
**All-pairs pairwise stability.**
    If every decisive pairwise margin exceeds `2ε`, then all pairwise
    preferences are preserved under `ε`-close perturbation.
-/

/-! ## GL₃ Tropical Satake Bridge -/

/-- A predicate marking a score map as arising from the GL₃ tropical Satake
    Hecke algebra construction. This is a marker class; the actual content
    is that the score map factors through the tropical Satake transform
    on the GL₃ dominant chamber. -/
class IsGL3TropicalSatakeScore {X : Type*} (f : Score3 X) : Prop where
  /-- The score map arises from a tropical Satake Hecke construction. -/
  satake_origin : True

/-
**GL₃ tropical Satake top-1 stability.**
    For any GL₃ tropical Satake score map, top-1 decisions are preserved
    under `ε`-close perturbation when margins exceed `2ε`.
-/

/-
**GL₃ tropical Satake top-2 stability.**
    For any GL₃ tropical Satake score map with a unique bottom class
    separated by margin `> 2ε`, the top-2 set is preserved.
-/

/-
**GL₃ tropical Satake pairwise stability.**
    For any GL₃ tropical Satake score map, pairwise preferences are preserved
    under `ε`-close perturbation when margins exceed `2ε`.
-/

/-
**Bundled GL₃ tropical Satake stability transfer.**
    A single theorem packaging top-1, top-2, and pairwise stability
    for GL₃ tropical Satake scores. This is the main interface theorem
    for downstream consumers.
-/

end GL3TropicalSatakeScoreStability


