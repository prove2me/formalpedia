-- Prove2me | solution 1 for TropicalSourceCoding.tropicalRateDistortion_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:34.583265+00:00
-- url     : https://prove2.me/submissions/3fa34e1f-903c-49b7-b977-8e488f9755db

-- Sol generated from Bridges/TropicalRateDistortionExact.lean
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

/-
**Min-plus convexity** of the rate-distortion function.
-/

/-
The distortion profile is antitone in the distortion kernel.
-/

/-
**Feasible set characterization**
-/


open TropicalSourceCoding in
theorem solution    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (φ : α → ℝ) (d : α → β → ℝ) (D : ℝ) (c : ℝ) :
    tropicalRateDistortion (fun x => φ x + c) d D =
      tropicalRateDistortion φ d D + c := by
  -- By definition of tropicalDistortionProfile, we have:
  have h_tropicalDistortionProfile_shift : ∀ y, tropicalDistortionProfile (fun x => φ x + c) d y = tropicalDistortionProfile φ d y + c := by
    unfold tropicalDistortionProfile;
    intro y;
    refine' le_antisymm _ _;
    · simp +decide [ add_sub_right_comm ];
      exact fun x => ⟨ x, by linarith ⟩;
    · simp +decide [ add_sub_right_comm ];
      have := Finset.exists_max_image Finset.univ ( fun x => φ x - d x y ) ⟨ Classical.arbitrary α, Finset.mem_univ _ ⟩ ; aesop;
  unfold tropicalRateDistortion;
  simp +decide [ h_tropicalDistortionProfile_shift, sub_add_eq_add_sub ];
  refine' le_antisymm _ _ <;> simp +decide [ Finset.inf'_le, Finset.le_inf' ];
  · simpa using Finset.exists_min_image Finset.univ ( fun y => tropicalDistortionProfile φ d y ) ⟨ Classical.arbitrary β, Finset.mem_univ _ ⟩;
  · exact fun y => ⟨ y, le_rfl ⟩
