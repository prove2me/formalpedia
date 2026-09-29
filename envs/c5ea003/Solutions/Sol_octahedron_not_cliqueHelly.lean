-- Prove2me | solution 1 for octahedron_not_cliqueHelly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:58:01.127971+00:00
-- url     : https://prove2.me/submissions/10a2dd4a-b240-4302-895f-4560b6a5b568

-- Sol generated from MachineLearning/RamseyTheory/OctahedronNotCliqueHelly.lean
import Mathlib
import Definitions.Def_MachineLearning_RamseyTheory_OctahedronNotCliqueHelly
import Theorems.Thm_octahedron_isMaxClique_024
import Theorems.Thm_octahedron_isMaxClique_035
import Theorems.Thm_octahedron_isMaxClique_125

/-!
# The octahedron graph `K_{2,2,2}` is not clique-Helly

This file gives a self-contained, minimal formalization of the fact that the
octahedron graph (the complete tripartite graph `K_{2,2,2}`) is **not**
clique-Helly.

The vertex set is `Fin 6`, split into three parts of size two according to
`i / 2`:

* part `0` = `{0, 1}`,
* part `1` = `{2, 3}`,
* part `2` = `{4, 5}`.

Two vertices are adjacent iff they are distinct and lie in different parts.

A graph is *clique-Helly* if every family of maximal cliques that pairwise
intersect has a common vertex.  We exhibit three maximal cliques
`{0,2,4}`, `{0,3,5}`, `{1,2,5}` that pairwise intersect but have empty total
intersection, witnessing the failure of the Helly property.
-/

open SimpleGraph







/-- The three maximal cliques pairwise intersect: `0 ∈ {0,2,4} ∩ {0,3,5}`,
`2 ∈ {0,2,4} ∩ {1,2,5}`, and `5 ∈ {0,3,5} ∩ {1,2,5}`. -/
lemma pairwise_intersect :
    ({0,2,4} : Set (Fin 6)) ∩ {0,3,5} ≠ ∅ ∧
    ({0,2,4} : Set (Fin 6)) ∩ {1,2,5} ≠ ∅ ∧
    ({0,3,5} : Set (Fin 6)) ∩ {1,2,5} ≠ ∅ :=
  ⟨Set.nonempty_iff_ne_empty.mp ⟨0, by simp⟩,
   Set.nonempty_iff_ne_empty.mp ⟨2, by simp⟩,
   Set.nonempty_iff_ne_empty.mp ⟨5, by simp⟩⟩

/-- The three maximal cliques have empty common intersection:
`{0,2,4} ∩ {0,3,5} = {0}` and `0 ∉ {1,2,5}`. -/
lemma total_intersection_empty :
    ({0,2,4} : Set (Fin 6)) ∩ ({0,3,5} ∩ {1,2,5}) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, h3⟩
  fin_cases x <;> simp_all


theorem solution: ¬ CliqueHelly octahedron := by
  intro h
  obtain ⟨p1, p2, p3⟩ := pairwise_intersect
  have n1 : (({0,2,4} : Set (Fin 6)) ∩ {0,3,5}).Nonempty := Set.nonempty_iff_ne_empty.mpr p1
  have n2 : (({0,2,4} : Set (Fin 6)) ∩ {1,2,5}).Nonempty := Set.nonempty_iff_ne_empty.mpr p2
  have n3 : (({0,3,5} : Set (Fin 6)) ∩ {1,2,5}).Nonempty := Set.nonempty_iff_ne_empty.mpr p3
  have hmax : ∀ s ∈ ({{0,2,4}, {0,3,5}, {1,2,5}} : Set (Set (Fin 6))),
      IsMaxClique octahedron s := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl|rfl|rfl
    · exact octahedron_isMaxClique_024
    · exact octahedron_isMaxClique_035
    · exact octahedron_isMaxClique_125
  have hpair : ∀ s₁ ∈ ({{0,2,4}, {0,3,5}, {1,2,5}} : Set (Set (Fin 6))),
      ∀ s₂ ∈ ({{0,2,4}, {0,3,5}, {1,2,5}} : Set (Set (Fin 6))), (s₁ ∩ s₂).Nonempty := by
    intro s1 hs1 s2 hs2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs1 hs2
    rcases hs1 with rfl|rfl|rfl <;> rcases hs2 with rfl|rfl|rfl
    · exact ⟨0, by simp⟩
    · exact n1
    · exact n2
    · exact Set.inter_comm _ _ ▸ n1
    · exact ⟨0, by simp⟩
    · exact n3
    · exact Set.inter_comm _ _ ▸ n2
    · exact Set.inter_comm _ _ ▸ n3
    · exact ⟨1, by simp⟩
  obtain ⟨x, hx⟩ := h _ hmax hpair
  rw [Set.mem_iInter₂] at hx
  have hA := hx {0,2,4} (by simp)
  have hB := hx {0,3,5} (by simp)
  have hC := hx {1,2,5} (by simp)
  have hmem : x ∈ ({0,2,4} : Set (Fin 6)) ∩ ({0,3,5} ∩ {1,2,5}) := ⟨hA, hB, hC⟩
  rw [total_intersection_empty] at hmem
  exact hmem
