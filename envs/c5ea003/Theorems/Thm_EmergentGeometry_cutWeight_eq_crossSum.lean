-- Prove2me | Theorems.Thm_EmergentGeometry_cutWeight_eq_crossSum
-- name    : EmergentGeometry.cutWeight_eq_crossSum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:34:59.285091+00:00
-- url     : https://prove2.me/theorems/7697e8ac-dca9-42a2-9009-da0d343f5539
-- title:
--   The area of the surface bounding a region, written as a one-sided sum over
-- statement:
--   The area of the surface bounding a region, written as a one-sided sum over
--   the pairs that cross it.
--
--   ```lean
--   theorem EmergentGeometry.cutWeight_eq_crossSum(G : BulkGraph V) (f : Region V) :
--       cutWeight G f = ∑ x, ∑ y, (if f x = true ∧ f y = false then G.weight x y else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EREPRBitThreads.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EREPRBitThreads.lean#L80

-- Thm stub generated from Novelty/EREPRBitThreads.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBitThreads
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

/-!
# Bit threads: flows through an Einstein–Rosen bridge

The Ryu–Takayanagi prescription used in `Novelty.EmergentGeometryEntropyCone`
measures entanglement by *cutting* the bulk.  The dual "bit thread" picture
measures it by *flowing* through the bulk: entanglement is the maximal number of
Planck-thickness threads that can be routed from one boundary region to the
other.  This file introduces flows (`BitThreads`) on a bulk geometry and proves
the duality inequality

  `value(flow) ≤ area(any separating surface)`,

hence `value ≤ throat`, together with a matching flow for the elementary
one-throat wormhole, where the bound is attained: **max-flow = min-cut for a
single Einstein–Rosen bridge**.

Main results:

* `cutWeight_eq_crossSum` — the area of a surface as a one-sided double sum
  (the form flows interact with).
* `sum_antisymm_zero` — an antisymmetric flow contributes nothing inside a
  region; only the flux through its boundary survives.
* `BitThreads.value_le_cutWeight`, `BitThreads.value_le_throat` — **weak
  duality**: no thread configuration can carry more than the cross-section of the
  bridge.
* `pairThreads_value`, `pairModel_maxflow_eq_throat` — the bound is sharp: the
  elementary wormhole of weight `w` admits threads of value exactly `w`, equal to
  its throat capacity and to half its mutual information.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  If ER=EPR is more than a slogan, the entanglement of
a boundary pair should be *transportable* through the bridge: there should exist
a divergence-free, capacity-respecting flow whose flux equals the bridge
cross-section.

EXPERIMENT (Experimenter).  Weak duality is a two-step computation: (i) the flux
out of the source region equals the flux out of *any* admissible region
containing it (conservation kills the extra cells), and (ii) the internal part of
that flux cancels by antisymmetry, leaving a boundary term bounded by the
capacities.  Both steps are `Finset` identities: `Finset.sum_subset` and the
antisymmetric-sum-vanishing lemma.

ANALYSIS (Analyst).  The proof never uses finiteness beyond summability, and
never uses symmetry of the weights except through `cutWeight_eq_crossSum`.  The
converse (strong duality, i.e. existence of a saturating flow in general) is a
max-flow–min-cut theorem and is left as an explicit open direction; we verify it
by hand in the one-throat case.

CRITIQUE (Critic).  `capacity` is stated one-sidedly (`flow x y ≤ weight x y`);
combined with `antisymm` and symmetry of `weight` this is equivalent to
`|flow x y| ≤ weight x y`, so nothing is lost, and the sharp example shows the
class of flows is not degenerate.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Areas as one-sided sums -/


omit [DecidableEq V] in

theorem EmergentGeometry.cutWeight_eq_crossSum(G : BulkGraph V) (f : Region V) :
    cutWeight G f = ∑ x, ∑ y, (if f x = true ∧ f y = false then G.weight x y else 0) := by sorry
