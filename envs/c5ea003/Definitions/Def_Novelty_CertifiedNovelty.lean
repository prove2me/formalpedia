-- Prove2me | Definitions.Def_Novelty_CertifiedNovelty
-- name    : Novelty_CertifiedNovelty
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:30.904366+00:00
-- url     : https://prove2.me/theorems/e515e7a9-799e-46af-8ac4-fd64279bd32b
-- title:
--   Aether Catalog definitions — Novelty_CertifiedNovelty
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CertifiedNovelty`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CertifiedNovelty.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Certified Novelty Detection in Metric Spaces

This file develops a quantitative theory of *novelty certification* in (pseudo)metric
spaces. The basic object is the predicate `IsNovel ε S x`, asserting that a point `x`
is `ε`-separated from every element of a reference set `S` ("everything already known").

We connect this qualitative predicate to a continuous *novelty score*
`noveltyScore S x = Metric.infDist x S`, prove its regularity (1-Lipschitz in the
point, antitone in the reference set), and establish two transport principles:

* **Robustness / triangle transfer** (`novel_triangle_transfer`): novelty degrades
  gracefully under perturbation of the query point.
* **Novelty transport under antilipschitz maps** (`novel_transport_antilipschitz`):
  novelty certificates survive *expanding* (lower-Lipschitz) embeddings, with the
  threshold scaling by the antilipschitz constant. Bi-Lipschitz maps therefore give
  faithful two-sided transport (`novel_transport_lipschitz_le`).

Finally we link novelty to *packing*: a mutually `ε`-separated reference set induces a
family of pairwise-disjoint balls of radius `ε/2` (`separated_balls_pairwiseDisjoint`),
the geometric core of all sphere-packing capacity bounds.

## Main results

* `isNovel_iff_le_noveltyScore` — `x` is `ε`-novel iff `ε ≤ noveltyScore S x`.
* `noveltyScore_lipschitz` — the novelty score is 1-Lipschitz in the query point.
* `noveltyScore_antitone` — the novelty score is antitone in the reference set.
* `novel_triangle_transfer` — perturbing the query by `δ` costs at most `δ` of novelty.
* `novel_transport_antilipschitz` — antilipschitz maps transport novelty.
* `separated_balls_pairwiseDisjoint` — mutual separation ⇒ disjoint half-radius balls.
-/

namespace CertifiedNovelty

open Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-! ## Core definitions -/

/-- `x` is **`ε`-novel** with respect to a reference set `S` if it is at distance at
least `ε` from every point of `S`. -/
def IsNovel (ε : ℝ) (S : Set α) (x : α) : Prop := ∀ s ∈ S, ε ≤ dist x s

/-- The **novelty score** of `x` relative to `S` is the distance from `x` to the set
`S`. For finite `S` this is `min_{s ∈ S} dist x s`; the general definition uses
`Metric.infDist`, inheriting all its regularity. -/
noncomputable def noveltyScore (S : Set α) (x : α) : ℝ := Metric.infDist x S

/-- A set `S` is **mutually `ε`-separated** if any two distinct points are at distance
at least `ε`. -/
def MutuallySeparated (ε : ℝ) (S : Set α) : Prop := S.Pairwise (fun a b => ε ≤ dist a b)

/-! ## Score characterization -/

-- !-- `IsNovel` unfolds to a lower bound on all distances, which is exactly the
-- content of `Metric.le_infDist` for nonempty sets. -- !--


/-! ## Regularity of the novelty score -/

-- !-- This is exactly `Metric.lipschitz_infDist_pt`: distance-to-a-set is
-- 1-Lipschitz in the point. -- !--


-- !-- Enlarging the reference set can only bring known points closer, so `infDist`
-- decreases; this is `Metric.infDist_le_infDist_of_subset`. -- !--


/-! ## Robustness: triangle transfer -/

-- !-- For `s ∈ S`, the triangle inequality gives
-- `dist y s ≥ dist x s - dist x y ≥ ε - δ`. -- !--

/-! ## Transport under maps -/

-- !-- Antilipschitz means `dist x s ≤ K * dist (f x) (f s)`, so
-- `dist (f x) (f s) ≥ dist x s / K ≥ ε / K`. -- !--

-- !-- Lipschitz maps contract distances, so the image distance is an upper bound on the
-- transported threshold; `dist (f x) (f s) ≤ K * dist x s`. -- !--

/-! ## Packing: separation yields disjoint balls -/

-- !-- Two points at distance `≥ ε` have disjoint open balls of radius `ε/2`, since
-- `ε/2 + ε/2 = ε ≤ dist`; apply `Metric.ball_disjoint_ball`. -- !--


/-! ## Bridge: separation ⇔ pointwise novelty -/

-- !-- Removing `x` from a separated set, every remaining point is `ε`-far from `x` by
-- definition of `MutuallySeparated`. -- !--

end CertifiedNovelty


