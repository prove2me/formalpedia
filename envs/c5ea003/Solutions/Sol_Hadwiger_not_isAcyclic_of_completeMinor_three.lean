-- Prove2me | solution 1 for Hadwiger.not_isAcyclic_of_completeMinor_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:35:38.746882+00:00
-- url     : https://prove2.me/submissions/0da97ed2-bd12-4087-9a26-7f823360b558

-- Sol generated from Probability/HadwigerForest.lean
import Mathlib
import Definitions.Def_Probability_ForestDensity
import Definitions.Def_Probability_HadwigerCore
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_MinorModel
import Theorems.Thm_Hadwiger_walkMinor_iff_isMinor
/-
  Forests are Exactly the `K₃`-Minor-Free Graphs
  ==============================================

  `ForestDensity.lean` established that forests are closed under *subgraphs* and
  listed the full contraction-closed statement — "forests `=` the class
  excluding `K₃` as a **minor**" — as the natural next target.  This file proves
  it, in both directions and with no finiteness hypothesis:

  * `Hadwiger.not_isAcyclic_of_completeMinor_three` : a graph with a `K₃` minor
                                            contains a cycle.  (Equivalently:
                                            forests are `K₃`-minor-free, so the
                                            class of forests really is
                                            minor-closed, not merely
                                            subgraph-closed.)
  * `Hadwiger.completeMinor_three_iff_not_isAcyclic` : `K₃ ≼ G ↔ G` has a cycle.
  * `Hadwiger.acyclicClass_eq_excl_K3`      : the catalog's `acyclicClass` is
                                            exactly the excluded-`K₃` class.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): acyclicity should be *minor*-closed, not just
    subgraph-closed; the obstruction to a direct proof is that contraction is not
    a subgraph operation.
  Experiment (Experimenter): rather than tracking contractions, we contradict the
    bridge characterisation of acyclicity: given a `K₃` model with linking edges
    `x₀x₁`, `y₀y₂`, `z₁z₂`, the route
    `x₀ ⇝ y₀ → y₂ ⇝ z₂ → z₁ ⇝ x₁` travels inside the branch sets and never uses
    the edge `x₀x₁`, so `x₀x₁` is not a bridge.
  Analysis (Analyst): every edge of that route has both endpoints inside a single
    branch set, or joins branch `0` to branch `2`, or branch `1` to branch `2`;
    disjointness of the branch sets rules out each of them being `x₀x₁`.  This is
    the only place where disjointness of a minor model is used essentially.
  Critique (Critic): the statement needs no finiteness and no decidability — the
    walks come from the walk-level connectivity of `HadwigerCore.lean`, and
    `Walk.toDeleteEdges` transports them into the edge-deleted graph.
  Synthesis (PI): combined with `completeMinor_three_of_not_isAcyclic` this gives
    a clean excluded-minor characterisation of forests, closing the milestone
    named in `ForestDensity.lean`.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}






open Hadwiger in
theorem solution(h : CompleteMinor 3 G) : ¬ G.IsAcyclic := by
  classical
  intro hacyc
  obtain ⟨M⟩ := walkMinor_iff_isMinor.mpr h
  obtain ⟨x0, hx0, x1, hx1, e01⟩ :=
    M.edge_lift (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide)
  obtain ⟨y0, hy0, y2, hy2, e02⟩ :=
    M.edge_lift (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by decide)
  obtain ⟨z1, hz1, z2, hz2, e12⟩ :=
    M.edge_lift (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide)
  -- each of `x₀`, `x₁` lies in exactly one branch set
  have hmem_unique : ∀ {c : V} {i j : Fin 3}, i ≠ j → c ∈ M.branch i → c ∉ M.branch j :=
    fun hij hc hcon => (Set.disjoint_left.mp (M.branch_disjoint hij)) hc hcon
  have hx1_0 : x1 ∉ M.branch 0 := hmem_unique (by decide) hx1
  have hx1_2 : x1 ∉ M.branch 2 := hmem_unique (by decide) hx1
  have hx0_1 : x0 ∉ M.branch 1 := hmem_unique (by decide) hx0
  have hx0_2 : x0 ∉ M.branch 2 := hmem_unique (by decide) hx0
  -- the deleted edge is a bridge
  have hbridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hacyc) e01
  have hnr : ¬ (G \ fromEdgeSet {s(x0, x1)}).Reachable x0 x1 :=
    (SimpleGraph.isBridge_iff.mp hbridge).2
  -- walks that stay inside a branch set never use the edge `x₀x₁`
  have hedge_of_walk : ∀ {a b : V} (p : G.Walk a b) (S : Set V),
      (∀ z ∈ p.support, z ∈ S) → (x0 ∉ S ∨ x1 ∉ S) →
      ∀ e, e ∈ p.edges → e ∉ ({s(x0, x1)} : Set (Sym2 V)) := by
    intro a b p S hsup hS e he hmem
    rw [Set.mem_singleton_iff] at hmem
    subst hmem
    rcases hS with hS | hS
    · exact hS (hsup _ (p.fst_mem_support_of_mem_edges he))
    · exact hS (hsup _ (p.snd_mem_support_of_mem_edges he))
  -- the three walks inside the branch sets
  obtain ⟨p0, hp0⟩ := (M.branch_connected 0).walk hx0 hy0
  obtain ⟨p2, hp2⟩ := (M.branch_connected 2).walk hy2 hz2
  obtain ⟨p1, hp1⟩ := (M.branch_connected 1).walk hz1 hx1
  -- the two crossing edges are not `x₀x₁` either
  have hcross02 : s(y0, y2) ∉ ({s(x0, x1)} : Set (Sym2 V)) := by
    rw [Set.mem_singleton_iff]
    intro hcon
    rcases Sym2.eq_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx1_2 hy2
    · exact hx1_0 hy0
  have hcross12 : s(z2, z1) ∉ ({s(x0, x1)} : Set (Sym2 V)) := by
    rw [Set.mem_singleton_iff]
    intro hcon
    rcases Sym2.eq_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx0_2 hz2
    · exact hx1_2 hz2
  -- assemble the detour avoiding `x₀x₁`
  refine hnr ?_
  have r0 : (G.deleteEdges {s(x0, x1)}).Reachable x0 y0 :=
    ⟨p0.toDeleteEdges _ (hedge_of_walk p0 _ hp0 (Or.inr hx1_0))⟩
  have r2 : (G.deleteEdges {s(x0, x1)}).Reachable y2 z2 :=
    ⟨p2.toDeleteEdges _ (hedge_of_walk p2 _ hp2 (Or.inr hx1_2))⟩
  have r1 : (G.deleteEdges {s(x0, x1)}).Reachable z1 x1 :=
    ⟨p1.toDeleteEdges _ (hedge_of_walk p1 _ hp1 (Or.inl hx0_1))⟩
  have a02 : (G.deleteEdges {s(x0, x1)}).Adj y0 y2 :=
    SimpleGraph.deleteEdges_adj.mpr ⟨e02, hcross02⟩
  have a12 : (G.deleteEdges {s(x0, x1)}).Adj z2 z1 :=
    SimpleGraph.deleteEdges_adj.mpr ⟨e12.symm, hcross12⟩
  exact ((((r0.trans a02.reachable).trans r2).trans a12.reachable).trans r1)
