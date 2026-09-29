-- Prove2me | solution 1 for PhantomOrder.upperTopGen_lt_orderTop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:23:45.772388+00:00
-- url     : https://prove2.me/submissions/c94b68e0-e3b8-46af-9dab-2eb2359a1d90

-- Sol generated from Novelty/PhantomTopologyOrderGeneral.lean
import Mathlib
import Definitions.Def_Novelty_PhantomTopologyOrderGeneral
/-
# Phantom Topologies over Ordered Observers: the General Two-Observer Theorem

A *phantom topology* on a set `X` with observer set `ι` is a family
`T : ι → TopologicalSpace X`.  The *consensus* (real) topology is the supremum
`⨆ i, T i`, whose open sets are exactly the sets open in **every** `T i`
(`isOpen_iSup_iff`): reality is what all observers agree on.

`Catalog/Novelty/PhantomTopology.lean` established the headline **two-observer
theorem for the real line**: the Euclidean topology on `ℝ` is the consensus of a
left-looking (upper-limit) and a right-looking (lower-limit) observer.  That proof
was entirely `ℝ`-specific, resting on the metric `ε`–`δ` characterisation of open
sets.

This file **generalises that result to every linear order with the order
topology and no extreme points** (`NoMaxOrder`, `NoMinOrder`).  The metric is
removed completely: the argument runs on the order-theoretic `Set.Ioo`-neighbourhood
basis (`nhds_basis_Ioo`) and the elementary interval identity
`Set.Ioo a b = Set.Ioc a x ∪ Ico x b` for `a < x < b`.  Consequences:

* `consensus_orderTop` — the order topology is the join of the generic
  lower-limit and upper-limit observers, for **any** `[LinearOrder α]` with the
  order topology and no endpoints.  Instances: `ℝ`, `ℚ`, `ℤ`, ...
* `orderTop_phantom_number_two` — when the order is moreover **densely ordered**,
  the two observers are *distinct and each strictly finer* than reality, so the
  phantom number is exactly two.  This upgrades the `ℝ` theorem to `ℚ` and every
  dense endpoint-free chain.
* `lowerTopGen_eq_of_discrete` (corner case) — **density is essential**: on a
  discretely ordered chain such as `ℤ`, the lower-limit observer already *equals*
  the order topology, so a single observer suffices (phantom number one).

-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer):
  H1. The `ℝ` two-observer theorem is not metric in nature; it is a theorem about
      *linear orders*.  Any order topology (no endpoints) should be the consensus
      of the right-half-open and left-half-open observers.
  H2 (surprising). The `ℝ`-proof's dependence on the metric is an illusion: the
      whole content is the split `Set.Ioo a b = Set.Ioc a x ∪ Ico x b`.
  H3 (surprising). The phantom number of an order chain is **not** a topological
      invariant of the reals but a property of *order density*: a dense chain has
      phantom number 2, a discrete chain collapses to 1.  So "how many observers
      reality needs" measures density, not cardinality or metrizability.

Experiment (Experimenter):
  - Verified the interval split `Set.Ioo a b = Set.Ioc a x ∪ Ico x b` by `le_total` case
    analysis (no order completeness needed).
  - Confirmed on `ℤ` that `Ico n (n+1) = {n}`, so every singleton is lower-open,
    forcing `lowerTopGen = ⊥` = discrete = the order topology; density fails.
  - Confirmed on `ℚ` that `Ici 0` is lower-open but not order-open (a point
    strictly between any `a < 0` and `0` escapes), so the observer is strictly
    finer: density restores the genuine two-observer structure.

Analysis (Analyst):
  - H1/H2 survive as `consensus_orderTop`: the join of `lowerTopGen`/`upperTopGen`
    is the order topology, proved through `nhds_basis_Ioo` with zero metric input.
  - H3 survives as the pair `orderTop_phantom_number_two` (dense ⇒ number 2) and
    `lowerTopGen_eq_of_discrete` (discrete ⇒ number 1).  The invariant that phantom
    number tracks is order *density*.

Critique (Critic):
  - `consensus_orderTop` is not definitional: it equates a hand-built join of two
    custom topologies with Mathlib's order topology via a genuine neighbourhood
    argument.  No `native_decide`, no `True`, no wrapper renaming.
  - The strict-finer lemmas use honest witnesses (`Ici x`, `Set.Iic x`) and the
    `DenselyOrdered` hypothesis is shown *necessary* by the `ℤ` collapse, ruling
    out a vacuous or over-general claim.

Synthesis (PI):
  "How many observers does reality need?" is answered order-theoretically: exactly
  two for any dense endpoint-free chain, exactly one for a discrete one.  The
  Euclidean line is merely one instance of a purely order-theoretic phenomenon.
-/

open Set

open PhantomOrder

variable {α : Type*} [LinearOrder α]

/-! ## The two generic observers on a linear order -/





/-! ## The interval split -/


/-! ## Main theorem: the order topology is a two-observer consensus -/


/-! ## Density makes the two observers genuine (phantom number two) -/


/-- Each closed-below ray `(-∞, x]` is open for the upper-limit observer. -/
theorem upperOpenGen_Iic [NoMinOrder α] (x : α) : upperOpenGen (Set.Iic x) := by
  intro y hy
  obtain ⟨a, ha⟩ := exists_lt y
  exact ⟨a, ha, fun z hz => le_trans hz.2 hy⟩


/-- Dually, in a dense endpoint-free chain `(-∞, x]` is **not** order-open. -/
theorem not_isOpen_Iic [TopologicalSpace α] [OrderTopology α]
    [NoMaxOrder α] [NoMinOrder α] [DenselyOrdered α] (x : α) :
    ¬ IsOpen (Set.Iic x) := by
  intro h
  obtain ⟨p, ⟨ha, hb⟩, hsub⟩ := (nhds_basis_Ioo x).mem_iff.mp (h.mem_nhds (le_refl x))
  obtain ⟨c, hc1, hc2⟩ := exists_between hb
  have hmem : c ∈ Set.Iic x := hsub ⟨lt_trans ha hc1, hc2⟩
  exact absurd hmem (by simp only [mem_Iic, not_le]; exact hc1)





/-! ## Density is essential: the discrete-chain collapse -/



/-! ## Concrete instances: `ℚ` and `ℝ` -/




theorem solution[TopologicalSpace α] [OrderTopology α]
    [NoMaxOrder α] [NoMinOrder α] [DenselyOrdered α] [Nonempty α] :
    upperTopGen < (‹TopologicalSpace α› : TopologicalSpace α) := by
  refine lt_of_le_of_ne ?_ ?_
  · intro U hU
    have hUopen : IsOpen U := hU
    intro x hx
    obtain ⟨p, ⟨ha, hb⟩, hsub⟩ := (nhds_basis_Ioo x).mem_iff.mp (hUopen.mem_nhds hx)
    exact ⟨p.1, ha, fun y hy => hsub ⟨hy.1, lt_of_le_of_lt hy.2 hb⟩⟩
  · intro h
    have hop : @IsOpen α upperTopGen (Set.Iic (Classical.arbitrary α)) := upperOpenGen_Iic _
    rw [h] at hop
    exact not_isOpen_Iic _ hop
