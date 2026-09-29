-- Prove2me | Theorems.Thm_Catalog_Novelty_TotalRainbowForest_monochromatic_admitsTRF_iff_isAcyclic
-- name    : Catalog.Novelty.TotalRainbowForest.monochromatic_admitsTRF_iff_isAcyclic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:17:26.374195+00:00
-- url     : https://prove2.me/theorems/e8661a85-9bc1-4168-86aa-b0d6dd001346
-- title:
--   Monochromatic corollary.
-- statement:
--   **Monochromatic corollary.**  If all edges of `G` share the colour `k0`, then
--   `G` admits a total rainbow forest iff `G` is an ordinary forest.
--
--   ```lean
--   theorem Catalog.Novelty.TotalRainbowForest.monochromatic_admitsTRF_iff_isAcyclic(G : SimpleGraph V) (col : Sym2 V → κ) (k0 : κ)
--       (hmono : ∀ e ∈ G.edgeSet, col e = k0) : AdmitsTRF G col ↔ G.IsAcyclic := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ColorClass.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ColorClass.lean#L64

-- Thm stub generated from Novelty/ColorClass.lean
import Mathlib
import Definitions.Def_Novelty_Defs

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

theorem Catalog.Novelty.TotalRainbowForest.monochromatic_admitsTRF_iff_isAcyclic(G : SimpleGraph V) (col : Sym2 V → κ) (k0 : κ)
    (hmono : ∀ e ∈ G.edgeSet, col e = k0) : AdmitsTRF G col ↔ G.IsAcyclic := by sorry
