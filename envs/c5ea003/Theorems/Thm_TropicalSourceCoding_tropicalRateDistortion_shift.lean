-- Prove2me | Theorems.Thm_TropicalSourceCoding_tropicalRateDistortion_shift
-- name    : TropicalSourceCoding.tropicalRateDistortion_shift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:48.33252+00:00
-- url     : https://prove2.me/theorems/25374169-af8f-4b88-b44d-e9dc2f99cbf9
-- title:
--   TropicalRateDistortion shift
-- statement:
--   Formal statement of `TropicalSourceCoding.tropicalRateDistortion_shift` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalSourceCoding.tropicalRateDistortion_shift    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
--       (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) (c : ℝ) :
--       tropicalRateDistortion (fun x => φ x + c) d D =
--         tropicalRateDistortion φ d D + c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalRateDistortionExact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalRateDistortionExact.lean#L253

-- Thm stub generated from Bridges/TropicalRateDistortionExact.lean
import Mathlib
import Definitions.Def_Bridges_TropicalRateDistortionExact
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

open TropicalSourceCoding

/-! ## Section 1: Core Definitions -/







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

theorem TropicalSourceCoding.tropicalRateDistortion_shift    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) (c : ℝ) :
    tropicalRateDistortion (fun x => φ x + c) d D =
      tropicalRateDistortion φ d D + c := by sorry
