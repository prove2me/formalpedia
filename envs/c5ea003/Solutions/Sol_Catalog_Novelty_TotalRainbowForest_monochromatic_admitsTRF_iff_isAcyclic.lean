-- Prove2me | solution 1 for Catalog.Novelty.TotalRainbowForest.monochromatic_admitsTRF_iff_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:29:00.967594+00:00
-- url     : https://prove2.me/submissions/811251eb-2389-4702-9785-6ee9753a82f3

-- Sol generated from Novelty/ColorClass.lean
import Mathlib
import Definitions.Def_Novelty_Defs
import Theorems.Thm_Catalog_Novelty_TotalRainbowForest_colorClass_le
import Theorems.Thm_Catalog_Novelty_TotalRainbowForest_hasMonoCycle_iff_exists_cyclic_colorClass

/-!
# The colour-class (forest) characterisation of total rainbow forests

This file justifies the name "total rainbow forest": an edge-colored graph
admits one exactly when **every colour class is a forest**.  As a consequence,
for a *monochromatic* graph admitting a total rainbow forest coincides with being
an ordinary forest.

-- !-- Lab Notes -- !--
Experiment (Experimenter):
  The bridge between "monochromatic cycle in `G`" and "cycle inside a colour
  class" is again `Walk.transfer`.  A monochromatic cycle of colour `k` is a
  cycle whose edges all live in `colorClass G col k`, and conversely any cycle in
  a colour class is a monochromatic cycle of `G`.

Analysis (Analyst):
  `hasMonoCycle_iff_exists_cyclic_colorClass` packages both transfers; negating it
  gives `admitsTRF_iff_forall_colorClass_acyclic`.  The monochromatic corollary
  identifies `colorClass G col k0` with `G` when `G` is `k0`-monochromatic, and
  every other colour class is edgeless (hence acyclic).

Critique (Critic):
  * These are genuine equivalences on arbitrary `V`, `κ`; the proofs use
    `Walk.transfer`, `Walk.IsCycle.transfer`, `push_neg`, and `IsAcyclic.anti`,
    not `decide`.
  * `monochromatic_admitsTRF_iff_isAcyclic` is non-trivial: the forward direction
    needs the colour-class-`= G` identity, the backward direction the anti-mono-
    tonicity of acyclicity.
-/

open Catalog.Novelty.TotalRainbowForest

open SimpleGraph

variable {V : Type*} {κ : Type*}


/-- **Forest characterisation.**  `G` admits a total rainbow forest iff every
colour class is a forest (acyclic). -/
theorem admitsTRF_iff_forall_colorClass_acyclic (G : SimpleGraph V) (col : Sym2 V → κ) :
    AdmitsTRF G col ↔ ∀ k, (colorClass G col k).IsAcyclic := by
  rw [AdmitsTRF, hasMonoCycle_iff_exists_cyclic_colorClass, not_exists]
  simp only [not_not]



open Catalog.Novelty.TotalRainbowForest in
theorem solution(G : SimpleGraph V) (col : Sym2 V → κ) (k0 : κ)
    (hmono : ∀ e ∈ G.edgeSet, col e = k0) : AdmitsTRF G col ↔ G.IsAcyclic := by
  rw [admitsTRF_iff_forall_colorClass_acyclic]
  constructor
  · intro h
    have heq : colorClass G col k0 = G := by
      ext v w
      simp only [colorClass, inf_adj, fromEdgeSet_adj, Set.mem_setOf_eq]
      exact ⟨fun ⟨h1, _, _⟩ => h1,
        fun h1 => ⟨h1, hmono _ ((mem_edgeSet _).2 h1), h1.ne⟩⟩
    rw [← heq]
    exact h k0
  · intro h k
    exact SimpleGraph.IsAcyclic.anti (colorClass_le G col k) h
