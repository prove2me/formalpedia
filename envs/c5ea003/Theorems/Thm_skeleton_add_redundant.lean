-- Prove2me | Theorems.Thm_skeleton_add_redundant
-- name    : skeleton_add_redundant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:41.062181+00:00
-- url     : https://prove2.me/theorems/c02e24a3-a31b-4de1-a801-db74be168c5e
-- title:
--   Redundant relations don't change the skeleton.
-- statement:
--   Redundant relations don't change the skeleton.
--
--   ```lean
--   theorem skeleton_add_redundant{n : ℕ} (P : HeckeSemiringPresentation n)
--       (r : TropRelation n)
--       (hredundant : ∀ v ∈ tropRelationLocus P.relations, r.satisfiedAt v) :
--       BuildingSkeleton ⟨r :: P.relations, P.base⟩ = BuildingSkeleton P := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/Skeleton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/Skeleton.lean#L164

-- Thm stub generated from Bridges/Skeleton.lean
import Mathlib
import Definitions.Def_Bridges_Skeleton
import Definitions.Def_Bridges_TropicalHecke_MinPlusAlgebra
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Satake Skeleton: Character Space Realization

This file establishes the **Tropical Satake Skeleton Reconstruction** theorem:
the normalized tropical character space of an idempotent semiring presentation
is realized as a polyhedral complex defined by tropicalized relations.

## Main results

* `charVectorMap_range_eq_skeleton` — characters biject onto the skeleton
* `rank2_satake_skeleton` — explicit skeleton for rank-2 Satake presentation
* `rank3_skeleton` — Weyl chamber skeleton for rank-3
* `skeleton_eq_of_same_locus` — presentation independence
* `skeleton_add_redundant` — redundant relations don't change the skeleton
-/

noncomputable section

open Set Function Finset MinPlusExpr

/-! ## §1. Hecke Semiring Presentations -/




/-! ## §2. Characters and the Realization Theorem -/







/-! ## §3. Hecke Generator Actions -/




/-! ## §4. Concrete Examples -/





/-! ## §5. Hecke Actions on Rank-2 -/



/-! ## §6. Presentation Independence -/

theorem skeleton_add_redundant{n : ℕ} (P : HeckeSemiringPresentation n)
    (r : TropRelation n)
    (hredundant : ∀ v ∈ tropRelationLocus P.relations, r.satisfiedAt v) :
    BuildingSkeleton ⟨r :: P.relations, P.base⟩ = BuildingSkeleton P := by sorry
