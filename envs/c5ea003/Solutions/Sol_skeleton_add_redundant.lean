-- Prove2me | solution 1 for skeleton_add_redundant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:25:57.89151+00:00
-- url     : https://prove2.me/submissions/7978ebd5-7d28-401d-89ba-e395ca718cd5

-- Sol generated from Bridges/Skeleton.lean
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



/-! ## §7. Eigencharacter Fixed-Point Connection -/




theorem solution{n : ℕ} (P : HeckeSemiringPresentation n)
    (r : TropRelation n)
    (hredundant : ∀ v ∈ tropRelationLocus P.relations, r.satisfiedAt v) :
    BuildingSkeleton ⟨r :: P.relations, P.base⟩ = BuildingSkeleton P := by
  ext v
  simp only [BuildingSkeleton, normalizedTropRelationLocus, Set.mem_inter_iff,
    NormalizedVectors, Set.mem_setOf_eq, tropRelationLocus]
  constructor
  · intro ⟨hrel, hbase⟩
    exact ⟨fun r' hr' => hrel r' (List.mem_cons_of_mem r hr'), hbase⟩
  · intro ⟨hrel, hbase⟩
    exact ⟨fun r' hr' => by
      rcases List.mem_cons.mp hr' with rfl | h
      · exact hredundant v hrel
      · exact hrel r' h, hbase⟩
