-- Prove2me | Definitions.Def_Novelty_EREPRBitThreads
-- name    : Novelty_EREPRBitThreads
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:23.075087+00:00
-- url     : https://prove2.me/theorems/97549410-7e39-4b94-a7c5-5966af4b99bc
-- title:
--   Aether Catalog definitions — Novelty_EREPRBitThreads
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EREPRBitThreads`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EREPRBitThreads.lean by skeleton subtraction
import Mathlib
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

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Areas as one-sided sums -/




/-! ## Bit threads -/

/-- A **bit thread configuration** on a bulk geometry: an antisymmetric flow
whose magnitude never exceeds the local area element. -/
structure BitThreads (G : BulkGraph V) where
  /-- The oriented flux carried from one cell to another. -/
  flow : V → V → ℝ
  /-- Threads are oriented: reversing the orientation reverses the flux. -/
  antisymm : ∀ x y, flow x y = -flow y x
  /-- No more threads may cross a surface element than its area. -/
  capacity : ∀ x y, flow x y ≤ G.weight x y

variable {G : BulkGraph V}

/-- The net flux emanating from a cell. -/
def BitThreads.div (T : BitThreads G) (x : V) : ℝ := ∑ y, T.flow x y

/-- Threads are conserved away from the sources `A` and the sinks `B`. -/
def BitThreads.Conserved (T : BitThreads G) (A B : Region V) : Prop :=
  ∀ v, A v = false → B v = false → T.div v = 0

/-- The total flux emitted by the source region. -/
def BitThreads.value (T : BitThreads G) (A : Region V) : ℝ :=
  ∑ x ∈ univ.filter (fun x => A x = true), T.div x



/-! ## Sharpness: threading the elementary wormhole -/

/-- The thread configuration carrying `w` units through the single throat of the
two-cell wormhole. -/
def pairThreads (w : ℝ) (hw : 0 ≤ w) : BitThreads (pairModel w hw).toBulkGraph where
  flow x y := if x = 0 ∧ y = 1 then w else if x = 1 ∧ y = 0 then -w else 0
  antisymm x y := by
    fin_cases x <;> fin_cases y <;> norm_num
  capacity x y := by
    fin_cases x <;> fin_cases y
    all_goals simp [pairModel]
    all_goals linarith




end EmergentGeometry


