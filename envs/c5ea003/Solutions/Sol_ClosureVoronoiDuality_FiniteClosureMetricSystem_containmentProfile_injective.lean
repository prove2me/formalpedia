-- Prove2me | solution 1 for ClosureVoronoiDuality.FiniteClosureMetricSystem.containmentProfile_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:04:27.932766+00:00
-- url     : https://prove2.me/submissions/a9cbd427-81dd-4b2a-ba1c-92f348080415

-- Sol generated from Bridges/ClosureVoronoiDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureVoronoiDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Closure-Voronoi Duality via Idempotent Metric Systems

## Overview

We establish a finite duality between algebraic closure operators and metric geometry.
The main result — the **Closure-Voronoi Duality Theorem** — shows that for a finite
closure metric system where closed balls are closure-fixed and ball families generate
the closure, membership `x ∈ cl(A)` is exactly equivalent to a geometric criterion:
`x` lies in every closed ball that contains `A`.

This provides a complete bridge:
- **Algebraic → Geometric**: closure data determines a canonical filtered nerve of balls.
- **Geometric → Algebraic**: the nerve incidence data reconstructs closure membership.

## Main results

* `closure_mem_iff_nerve_cover` — **Main Reconstruction Theorem**:
  `x ∈ cl(A) ↔ nerveCoverCriterion A x`.
* `ball_generated_extensional` — **Extensionality**: ball-generated sets are uniquely
  determined by their ball-containment profile.
* `nerve_face_of_pairwise` — **Helly Upgrade**: pairwise ball intersections yield
  full nerve faces under the Helly property.
* `nerveFaces_mono` — Nerve faces are monotone in radius.
* `certified_reconstruction_exists` — Existence of a certified closure decision procedure.
* `cl_isBallGenerated` — Every closure image is ball-generated.
* `containmentProfile_injective` — The containment profile is a complete invariant for
  ball-generated closed sets.
-/

open ClosureVoronoiDuality


variable {G R : Type*} [Fintype G] [DecidableEq G] [LinearOrder R] [Fintype R]

open FiniteClosureMetricSystem

variable (X : FiniteClosureMetricSystem G R)

/-! ### Core Definitions -/










/-! ### Ball Monotonicity -/


/-! ### Closure–Ball Interaction -/



/-! ### The Main Reconstruction Theorem -/




/-! ### Ball-Generated Sets and Extensionality -/


/-- **Extensionality Theorem for Ball-Generated Sets.**

Two ball-generated sets with identical ball-containment profiles are equal.
This means the geometric incidence data (which balls contain a set)
uniquely determines ball-generated closed sets. -/
theorem ball_generated_extensional {C₁ C₂ : Set G}
    (h₁ : X.isBallGenerated C₁) (h₂ : X.isBallGenerated C₂)
    (h : ∀ r g, C₁ ⊆ X.ball r g ↔ C₂ ⊆ X.ball r g) :
    C₁ = C₂ := by
  ext x
  constructor
  · intro hx
    apply h₂
    intro r g hC₂
    exact ((h r g).mpr hC₂) hx
  · intro hx
    apply h₁
    intro r g hC₁
    exact ((h r g).mp hC₁) hx


/-! ### Helly-Powered Nerve Reconstruction -/


/-! ### Nerve Monotonicity -/


/-! ### Critical Radii -/


/-! ### Certified Reconstruction -/


/-! ### Closure of Ball-Generated Sets -/



/-! ### Singleton Nerve Faces -/


/-! ### Closure Monotonicity Consequences -/



/-! ### Reconstruction From Ball Data -/




open ClosureVoronoiDuality in
theorem solution{C₁ C₂ : Set G}
    (h₁ : X.isBallGenerated C₁) (h₂ : X.isBallGenerated C₂)
    (h : X.containmentProfile C₁ = X.containmentProfile C₂) :
    C₁ = C₂ := by
  apply Set.Subset.antisymm
  · intro x hx
    refine h₂ x (fun r g hsub => ?_)
    have hiff : (C₁ ⊆ X.ball r g) ↔ (C₂ ⊆ X.ball r g) :=
      Iff.of_eq (congrFun (congrFun h r) g)
    exact hiff.mpr hsub hx
  · intro x hx
    refine h₁ x (fun r g hsub => ?_)
    have hiff : (C₁ ⊆ X.ball r g) ↔ (C₂ ⊆ X.ball r g) :=
      Iff.of_eq (congrFun (congrFun h r) g)
    exact hiff.mp hsub hx
