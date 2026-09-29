-- Prove2me | Definitions.Def_Novelty_PhantomTopologyOrderGeneral
-- name    : Novelty_PhantomTopologyOrderGeneral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:35:55.507994+00:00
-- url     : https://prove2.me/theorems/0e8b5312-201b-462b-8f42-cc623cd28eac
-- title:
--   Aether Catalog definitions — Novelty_PhantomTopologyOrderGeneral
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PhantomTopologyOrderGeneral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PhantomTopologyOrderGeneral.lean by skeleton subtraction
import Mathlib
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

namespace PhantomOrder

variable {α : Type*} [LinearOrder α]

/-! ## The two generic observers on a linear order -/

/-- The **lower-limit observer**'s open predicate: every point of `U` is the left
end of a right half-open interval `[x, b)` contained in `U`. -/
def lowerOpenGen (U : Set α) : Prop := ∀ x ∈ U, ∃ b, x < b ∧ Ico x b ⊆ U

/-- The **upper-limit observer**'s open predicate: every point of `U` is the right
end of a left half-open interval `(a, x]` contained in `U`. -/
def upperOpenGen (U : Set α) : Prop := ∀ x ∈ U, ∃ a, a < x ∧ Set.Ioc a x ⊆ U

/-- The generic lower-limit (Sorgenfrey) topology on a linear order without a
maximum. -/
def lowerTopGen [NoMaxOrder α] : TopologicalSpace α where
  IsOpen := lowerOpenGen
  isOpen_univ := fun x _ => let ⟨b, hb⟩ := exists_gt x; ⟨b, hb, by simp⟩
  isOpen_inter s t hs ht := by
    intro x hx
    obtain ⟨b1, hb1, hs1⟩ := hs x hx.1
    obtain ⟨b2, hb2, ht2⟩ := ht x hx.2
    refine ⟨min b1 b2, lt_min hb1 hb2, ?_⟩
    intro y hy
    exact ⟨hs1 ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩,
           ht2 ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩⟩
  isOpen_sUnion S hS := by
    intro x hx
    obtain ⟨U, hUS, hxU⟩ := hx
    obtain ⟨b, hb, hsub⟩ := hS U hUS x hxU
    exact ⟨b, hb, fun y hy => ⟨U, hUS, hsub hy⟩⟩

/-- The generic upper-limit topology on a linear order without a minimum. -/
def upperTopGen [NoMinOrder α] : TopologicalSpace α where
  IsOpen := upperOpenGen
  isOpen_univ := fun x _ => let ⟨a, ha⟩ := exists_lt x; ⟨a, ha, by simp⟩
  isOpen_inter s t hs ht := by
    intro x hx
    obtain ⟨a1, ha1, hs1⟩ := hs x hx.1
    obtain ⟨a2, ha2, ht2⟩ := ht x hx.2
    refine ⟨max a1 a2, max_lt ha1 ha2, ?_⟩
    intro y hy
    exact ⟨hs1 ⟨lt_of_le_of_lt (le_max_left _ _) hy.1, hy.2⟩,
           ht2 ⟨lt_of_le_of_lt (le_max_right _ _) hy.1, hy.2⟩⟩
  isOpen_sUnion S hS := by
    intro x hx
    obtain ⟨U, hUS, hxU⟩ := hx
    obtain ⟨a, ha, hsub⟩ := hS U hUS x hxU
    exact ⟨a, ha, fun y hy => ⟨U, hUS, hsub hy⟩⟩

/-! ## The interval split -/


/-! ## Main theorem: the order topology is a two-observer consensus -/


/-! ## Density makes the two observers genuine (phantom number two) -/









/-! ## Density is essential: the discrete-chain collapse -/



/-! ## Concrete instances: `ℚ` and `ℝ` -/



end PhantomOrder


