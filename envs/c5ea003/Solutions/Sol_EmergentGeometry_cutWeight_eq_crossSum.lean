-- Prove2me | solution 1 for EmergentGeometry.cutWeight_eq_crossSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:31:59.033806+00:00
-- url     : https://prove2.me/submissions/1161cdd9-f671-4d4a-89f6-7e7e9859bf76

-- Sol generated from Novelty/EREPRBitThreads.lean
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




/-! ## Bit threads -/


variable {G : BulkGraph V}






/-! ## Sharpness: threading the elementary wormhole -/






open EmergentGeometry in
omit [DecidableEq V] in
theorem solution(G : BulkGraph V) (f : Region V) :
    cutWeight G f = ∑ x, ∑ y, (if f x = true ∧ f y = false then G.weight x y else 0) := by
  have h1 : ∀ x y : V, (sepBit (f x) (f y) : ℝ) * G.weight x y
      = (if f x = true ∧ f y = false then G.weight x y else 0)
        + (if f y = true ∧ f x = false then G.weight x y else 0) := by
    intro x y; cases hx : f x <;> cases hy : f y <;> simp [sepBit]
  have h2 : ∑ x, ∑ y, (if f y = true ∧ f x = false then G.weight x y else 0)
      = ∑ x, ∑ y, (if f x = true ∧ f y = false then G.weight x y else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [G.weight_symm]
  rw [cutWeight, Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => h1 x y)),
    Finset.sum_congr rfl (fun x (_ : x ∈ univ) => Finset.sum_add_distrib),
    Finset.sum_add_distrib, h2]
  ring
