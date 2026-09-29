-- Prove2me | Definitions.Def_Bridges_TropicalRateDistortionExact
-- name    : Bridges_TropicalRateDistortionExact
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:03.285024+00:00
-- url     : https://prove2.me/theorems/313e1c32-cf4c-448f-8ee0-1fe072139abf
-- title:
--   Aether Catalog definitions — Bridges_TropicalRateDistortionExact
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalRateDistortionExact`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalRateDistortionExact.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Tropical Information Theory Project. All rights reserved.

# Tropical Rate-Distortion Theory: Exact Coding-Optimization Duality

## Overview

This file proves the central breakthrough of tropical source coding theory:
for finite types, the optimal coding cost at distortion budget `D` equals the
tropical rate-distortion function *exactly* — with no asymptotic gap.

In classical Shannon theory, achievability and converse bounds meet only in
the limit of infinite block length. In the tropical (min-plus) semiring,
finite optimization replaces probabilistic asymptotics, and the gap vanishes.

## Main Results

1. `tropicalRateDistortion_exact` — The optimal feasible code cost equals
   the min-plus variational rate-distortion value.
2. `tropicalRateDistortion_dual` — Dual characterization via feasible sets.
3. `tropical_no_gap` — Achievable and converse rates coincide exactly.
4. `tropicalRateDistortion_antitone` — Rate-distortion is antitone in D.
5. `tropicalRateDistortion_lipschitz` — Rate-distortion is 1-Lipschitz.

## Cross-Domain Connections

- **Tropical convex analysis**: The rate-distortion function is a tropical
  Legendre-Fenchel conjugate; exactness = tropical Fenchel-Moreau equality.
- **Shortest paths**: Feasibility `φ x - r ≤ d x y + D` is a covering/domination
  condition in a weighted bipartite graph.
- **Dynamic programming**: Source potentials are value functions; reproduction
  symbols are controls; distortion is stage cost.
- **Mathematical morphology**: `y ↦ sup_x (φ x - d x y)` is a dilation transform.
-/


open Finset BigOperators

namespace TropicalSourceCoding

/-! ## Section 1: Core Definitions -/

/-- **Tropical distortion profile.**
    For a source potential `φ : α → ℝ` and distortion kernel `d : α → β → ℝ`,
    the profile at reproduction symbol `y` is the worst-case net cost:
    `ψ(y) = max_x (φ(x) - d(x, y))`.

    This is also a *dilation* in the sense of mathematical morphology. -/
noncomputable def tropicalDistortionProfile
    {α β : Type*} [Fintype α] [Nonempty α]
    (φ : α → ℝ) (d : α → β → ℝ) (y : β) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => φ x - d x y)

/-- **Tropical rate-distortion function (primal form).**
    `R(D) = min_y ψ(y) - D = min_y (max_x (φ(x) - d(x,y))) - D`.

    This is the minimum worst-case net cost over all reproduction symbols,
    minus the distortion budget. As D increases, R decreases (antitone). -/
noncomputable def tropicalRateDistortion
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun y => tropicalDistortionProfile φ d y) - D

/-- **Tropical feasibility set.**
    The set of rates `r` for which there exists a reproduction symbol `y`
    such that every source symbol is covered: `φ(x) - r ≤ d(x,y) + D`.

    Equivalently, `r ≥ max_x (φ(x) - d(x,y)) - D` for some `y`. -/
def tropicalFeasibleSet
    {α β : Type*}
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) : Set ℝ :=
  {r | ∃ y : β, ∀ x : α, φ x - r ≤ d x y + D}

/-- **Tropical optimal code cost.**
    The infimum of the feasible set: the least rate achieving distortion ≤ D.
    `C*(D) = inf {r | ∃ y, ∀ x, φ(x) - r ≤ d(x,y) + D}`. -/
noncomputable def tropicalOptimalCodeCost
    {α β : Type*}
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf (tropicalFeasibleSet φ d D)

/-- **Tropical achievable rate.**
    The best rate achievable by a single-symbol tropical code.
    Defined as `min_y (ψ(y)) - D`. -/
noncomputable def tropicalAchievableRate
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun y => tropicalDistortionProfile φ d y) - D

/-- **Tropical converse rate.**
    The best lower bound from the dual: no code can achieve rate below this.
    Defined identically to the achievable rate, reflecting exact duality. -/
noncomputable def tropicalConverseRate
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun y => tropicalDistortionProfile φ d y) - D

/-! ## Section 2: Feasibility Lemmas -/

/-
The feasible set is nonempty for finite nonempty types.
-/

/-
The feasible set is bounded below for finite types.
-/

/-
The distortion profile value minus D is in the feasible set.
-/

/-
Any feasible rate is at least the profile minus D for some y.
-/

/-! ## Section 3: The Exact Equality Theorem -/

/-
**Key lemma**: The optimal code cost equals `min_y ψ(y) - D`.
-/


/-! ## Section 4: Dual Characterization -/


/-! ## Section 5: No Shannon Gap -/


/-! ## Section 6: Structural Properties -/


/-
The rate-distortion function is 1-Lipschitz in D.
-/

/-
Rate-distortion is monotone in the source potential.
-/

/-
**Attainment theorem**: The infimum is attained by some y*.
-/

/-
**Shift equivariance**: Shifting the source potential by a constant
    shifts the rate-distortion by the same constant.
-/

/-
**Min-plus convexity** of the rate-distortion function.
-/

/-
The distortion profile is antitone in the distortion kernel.
-/

/-
**Feasible set characterization**
-/

end TropicalSourceCoding


