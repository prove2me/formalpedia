-- Prove2me | solution 1 for SheafDatabaseGluing.compatible_has_unique_glue
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:10:50.37767+00:00
-- url     : https://prove2.me/submissions/006dc261-1cd2-42e0-a6ef-bfc1a74e7d97

-- Sol generated from Algebra/SheafDatabaseGluing.lean
import Mathlib
import Definitions.Def_Algebra_SheafDatabaseGluing

/-!
# Sheaf-Theoretic Database Gluing

A database view on a set `U` of columns is represented by a dependent function
assigning a value to every column in `U`.  Two views are compatible when their
values agree on `U ∩ V`.  This file proves, in a cumulative chain, the concrete
sheaf gluing theorem for such database views:

1. the canonical glued view restricts to the first view;
2. compatibility makes it restrict to the second view as well;
3. therefore a common extension exists;
4. that common extension is unique.

This is the sheaf condition for the sheaf of dependent records on a discrete
set of columns.  It formalizes the deterministic consistency claim without
assuming a probabilistic missing-data model.
-/

open Classical

open SheafDatabaseGluing

variable {ι : Type*} (Value : ι → Type*)




/-- The canonical glue always restricts to the first local record. -/
theorem glue_restrict_left {U V : Set ι} (s : LocalSection Value U)
    (t : LocalSection Value V) (i : ι) (hiU : i ∈ U) :
    glue Value s t i (Set.mem_union_left V hiU) = s i hiU := by
  rw [glue, dif_pos hiU]

/-- If the records agree on their overlap, the same canonical glue also
restricts to the second local record.  This theorem uses
`glue_restrict_left` in the overlap case. -/
theorem glue_restrict_right {U V : Set ι} (s : LocalSection Value U)
    (t : LocalSection Value V) (hcompat : Compatible Value s t)
    (i : ι) (hiV : i ∈ V) :
    glue Value s t i (Set.mem_union_right U hiV) = t i hiV := by
  by_cases hiU : i ∈ U
  · exact (glue_restrict_left Value s t i hiU).trans (hcompat i hiU hiV)
  · simp [glue, hiU]

/-- Compatible partial database records admit a common record on the union of
their columns. -/
theorem compatible_has_glue {U V : Set ι} (s : LocalSection Value U)
    (t : LocalSection Value V) (hcompat : Compatible Value s t) :
    ∃ u : LocalSection Value (U ∪ V),
      (∀ i (hiU : i ∈ U), u i (Set.mem_union_left V hiU) = s i hiU) ∧
      (∀ i (hiV : i ∈ V), u i (Set.mem_union_right U hiV) = t i hiV) := by
  refine ⟨glue Value s t, ?_, ?_⟩
  · exact fun i hiU => glue_restrict_left Value s t i hiU
  · exact fun i hiV => glue_restrict_right Value s t hcompat i hiV



open SheafDatabaseGluing in
theorem solution{U V : Set ι}
    (s : LocalSection Value U) (t : LocalSection Value V)
    (hcompat : Compatible Value s t) :
    ∃! u : LocalSection Value (U ∪ V),
      (∀ i (hiU : i ∈ U), u i (Set.mem_union_left V hiU) = s i hiU) ∧
      (∀ i (hiV : i ∈ V), u i (Set.mem_union_right U hiV) = t i hiV) := by
  obtain ⟨u, hu_left, hu_right⟩ := compatible_has_glue Value s t hcompat
  refine ⟨u, ⟨hu_left, hu_right⟩, ?_⟩
  intro v hv
  funext i hi
  by_cases hiU : i ∈ U
  · have heq : hi = Set.mem_union_left V hiU := by aesop
    rw [heq]
    exact (hv.1 i hiU).trans (hu_left i hiU).symm
  · have hiV : i ∈ V := by simpa [hiU] using hi
    have heq : hi = Set.mem_union_right U hiV := by aesop
    rw [heq]
    exact (hv.2 i hiV).trans (hu_right i hiV).symm
