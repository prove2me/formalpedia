-- Prove2me | Theorems.Thm_ShadowDecay_shadowProfile_union_le
-- name    : ShadowDecay.shadowProfile_union_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:12:32.709766+00:00
-- url     : https://prove2.me/theorems/9afe383a-04c1-46bd-a4bd-be028c03a9ec
-- title:
--   Shadow profile is subadditive under union.
-- statement:
--   Shadow profile is subadditive under union.
--
--   ```lean
--   theorem ShadowDecay.shadowProfile_union_le(S₁ S₂ : Finset (Fin n → ℕ)) (k : ℕ) :
--       shadowProfile (S₁ ∪ S₂) k ≤ shadowProfile S₁ k + shadowProfile S₂ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/ShadowDecay.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/ShadowDecay.lean#L207

-- Thm stub generated from Bridges/GraphTheory/ShadowDecay.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_ShadowDecay
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Shadow Decay Profiles for Algebraic Circuit Lower Bounds

This file introduces the **shadow decay profile** as a new complexity invariant
for multivariate polynomials, connecting algebraic circuit complexity to the
combinatorial geometry of polynomial supports.

## Main Definitions

* `ShadowDecay.totalDeg` — Total degree of a multi-index.
* `ShadowDecay.kthShadow` — The k-th downward shadow of a finite support set.
* `ShadowDecay.shadowProfile` — The shadow profile `k ↦ |Shadow_k(S)|`.
* `ShadowDecay.degreeSimplex` — The set of multi-indices with total degree ≤ d.
* `ShadowDecay.circuitShadowEnvelope` — Upper envelope for circuit-bounded supports.
* `ShadowDecay.HasSlowShadowDecay` — Predicate for supports with slow shadow decay.
* `ShadowDecay.elemSymmSupport` — Support of elementary symmetric polynomials.

## Main Results

* `ShadowDecay.kthShadow_subset_degreeSimplex` — Shadows stay inside lower-degree simplices.
* `ShadowDecay.shadowProfile_le_degreeSimplex_card` — Shadow profile bounded by simplex size.
* `ShadowDecay.kthShadow_elemSymm_eq` — Exact shadow characterization for elem. symm. supports.
* `ShadowDecay.shadowProfile_elemSymm` — Exact shadow profile for elementary symmetric supports.

## Cross-Domain Connections

This development bridges:
- **Algebraic complexity theory**: circuit lower bounds via support invariants
- **Extremal combinatorics**: shadow phenomena for set families (Kruskal–Katona)
- **Discrete convex geometry**: Newton polytope contraction under differentiation
- **Geometric complexity theory**: combinatorial front-end to orbit-closure methods
-/

open Finset BigOperators

open ShadowDecay

variable {n : ℕ}

/-! ## Total Degree for Multi-indices -/




/-! ## Degree Simplex -/



/-! ## k-th Shadow Definition -/



/-! ## Basic Shadow Properties -/




/-! ## Shadow Profile -/



/-! ## Circuit Shadow Envelope -/


/-! ## Slow Shadow Decay Predicate -/


/-! ## Theorem: Shadow Containment in Degree Simplex -/




/-! ## Shadow Profile Monotonicity -/


/-! ## Shadow Profile Subadditivity -/

theorem ShadowDecay.shadowProfile_union_le(S₁ S₂ : Finset (Fin n → ℕ)) (k : ℕ) :
    shadowProfile (S₁ ∪ S₂) k ≤ shadowProfile S₁ k + shadowProfile S₂ k := by sorry
