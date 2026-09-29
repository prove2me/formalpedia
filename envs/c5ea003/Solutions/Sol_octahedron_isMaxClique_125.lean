-- Prove2me | solution 1 for octahedron_isMaxClique_125
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:39.707546+00:00
-- url     : https://prove2.me/submissions/db4ea424-3d83-41b4-8866-210366399035

-- Sol generated from MachineLearning/RamseyTheory/OctahedronNotCliqueHelly.lean
import Mathlib
import Definitions.Def_MachineLearning_RamseyTheory_OctahedronNotCliqueHelly

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










theorem solution: IsMaxClique octahedron {1, 2, 5} := by
  constructor
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    refine ⟨hxy, ?_⟩
    rcases hx with h|h|h <;> rcases hy with h'|h'|h' <;> subst h <;> subst h' <;> simp_all
  · intro T hT hcl
    obtain ⟨w, hwT, hw⟩ := Set.exists_of_ssubset hT
    have hsub := hT.subset
    have h1 : (1 : Fin 6) ∈ T := hsub (by simp)
    have h2 : (2 : Fin 6) ∈ T := hsub (by simp)
    have h5 : (5 : Fin 6) ∈ T := hsub (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    push_neg at hw
    obtain ⟨hw1, hw2, hw5⟩ := hw
    fin_cases w <;> simp_all
    · exact (hcl h1 hwT (by decide)).2 (by decide)
    · exact (hcl h2 hwT (by decide)).2 (by decide)
    · exact (hcl h5 hwT (by decide)).2 (by decide)
