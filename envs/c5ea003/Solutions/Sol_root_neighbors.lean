-- Prove2me | solution 1 for root_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:41:06.838137+00:00
-- url     : https://prove2.me/submissions/cdc80bfd-62d0-4ce0-bc13-60868d379a70

-- Sol generated from Geometry/BerggrenRamanujan.lean
import Mathlib
import Definitions.Def_Geometry_BerggrenRamanujan

open Matrix

/-! # CatalogBuild.Pythagorean.Berggren.BerggrenRamanujan

Auto-generated from theorem catalog database.
Domain: Pythagorean/Berggren
Declarations: 59
-/

noncomputable section





























































theorem solution:
    {q : BPos | berggrenAdj [] q} = {[BDir.left], [BDir.mid], [BDir.right]} := by
  ext q
  simp only [berggrenAdj, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
             List.nil_append]
  constructor
  · rintro (⟨d, rfl⟩ | ⟨d, h⟩)
    · cases d <;> simp
    · simp at h
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨BDir.left, rfl⟩
    · exact Or.inl ⟨BDir.mid, rfl⟩
    · exact Or.inl ⟨BDir.right, rfl⟩
