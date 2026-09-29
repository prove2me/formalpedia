-- Prove2me | solution 1 for CliqueComplexFlag.flag_not_cliqueComplex_without_singletons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:40.59357+00:00
-- url     : https://prove2.me/submissions/b96e4085-27a4-422e-88a3-39e22bb8bfee

-- Sol generated from Geometry/RamseyTheory/CliqueComplexFlag.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
import Theorems.Thm_CliqueComplexFlag_mem_cliqueComplex
/-
# Clique Complexes, Flag Complexes, and the Vietoris–Rips Filtration

This file develops, from scratch, a lightweight theory of abstract simplicial
complexes (`ASC`) and the clique-complex construction on simple graphs, together
with the flag-complex characterization, the Vietoris–Rips filtration, and a
Turán-style bound on the `f`-vector.

## Main results

* `isClique_pair`            — a two-element set is a clique iff its endpoints are adjacent.
* `cliqueComplex_isFlag`     — every clique complex is a flag complex.
* `oneSkeleton_cliqueComplex`— the one-skeleton of `Δ(G)` is exactly `G`.
* `flag_eq_cliqueComplex`    — every flag complex *with all singletons* is the clique
                               complex of its own one-skeleton (the converse direction).
* `vietorisRips_mono`        — the Vietoris–Rips complex is monotone in the scale `ε`.
* `cliqueComplex_fVector_le_choose` — `f_k(Δ(G)) ≤ C(n, k+1)` (Turán-style upper bound).
* `flag_not_cliqueComplex_without_singletons` — the singleton hypothesis in
                               `flag_eq_cliqueComplex` cannot be dropped (counterexample).

-- !-- Lab Notebook -- !--
Hypothesis: the clique-complex and one-skeleton constructions form an
  adjunction-like pair on simple graphs, with flag complexes the image of `Δ`.
Result: proved both directions, with the precise side condition (all singletons
  present) isolated by an explicit counterexample on `Bool`.
Insight: the entire theory pivots on the single fact `isClique_pair`
  ("a 2-clique is an edge"); the forward direction is downward closure and the
  converse rebuilds a face from its edges via the flag axiom.
Failure analysis: the naive converse (drop the singleton hypothesis) is FALSE —
  clique complexes always contain every singleton, but a flag complex need not,
  witnessed by the trivial complex `{∅}` whose one-skeleton is the empty graph.
-- !-- Lab Notebook -- !--
-/

open CliqueComplexFlag

open scoped Classical

universe u
variable {V : Type u}


open ASC



/-! ## The clique complex of a simple graph -/




/-! ## The one-skeleton of a complex -/




/-! ## Flag complexes -/




/-! ## The Vietoris–Rips complex -/




/-! ## The f-vector and a Turán-style bound -/



/-! ## The singleton hypothesis is necessary -/




open CliqueComplexFlag in
theorem solution:
    IsFlag trivialComplex ∧
      trivialComplex ≠ cliqueComplex (oneSkeleton trivialComplex) := by
  -- !-- `{∅}` is vacuously flag; its one-skeleton is the empty graph, whose clique
  --     complex contains `{true}`, a non-face of `{∅}`. -- !--
  constructor
  · -- flagness: only the empty set can satisfy "all singletons are faces"
    intro s hsing _
    rcases Finset.eq_empty_or_nonempty s with h | h
    · subst h; simp [trivialComplex]
    · obtain ⟨u, hu⟩ := h
      have hu' := hsing u hu
      simp only [trivialComplex, Set.mem_singleton_iff] at hu'
      exact absurd hu' (Finset.singleton_ne_empty u)
  · intro hcontra
    have h1 : ({true} : Finset Bool) ∈ (cliqueComplex (oneSkeleton trivialComplex)).faces := by
      rw [mem_cliqueComplex]
      rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    rw [← hcontra] at h1
    simp only [trivialComplex, Set.mem_singleton_iff] at h1
    exact absurd h1 (by simp)
