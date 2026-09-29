-- Prove2me | Definitions.Def_Bridges_PosetTheory_GuardedFixedPointIndex
-- name    : Bridges_PosetTheory_GuardedFixedPointIndex
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:54.403275+00:00
-- url     : https://prove2.me/theorems/c56feaf0-3b7d-4fff-b449-914ad106b849
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_GuardedFixedPointIndex
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.GuardedFixedPointIndex`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/GuardedFixedPointIndex.lean by skeleton subtraction
import Mathlib

/-!
# Guarded Fixed-Point Index Theory

## Overview

This file develops a quantitative obstruction theory for guarded self-reference in
reversible temporal computation. The central idea is to attach a numerical index —
the **guarded fixed-point index** — to any guarded endomorphism, measuring the
irreducible feedback cost required to realize a fixed point.

Classical Lawvere-style diagonal arguments tell us *whether* a fixed point exists.
The guarded fixed-point index tells us *how much* guarded delay / closure weight
is irreducibly required, turning self-reference from a yes/no phenomenon into a
quantitative certificate.

## Main definitions

* `GuardedEnd α` — a guarded endomorphism on type `α`, carrying a morphism `f : α → α`,
  an oracle level, and a guard cost in `WithTop ℕ`.
* `RealizesAt g k` — the realizability predicate: budget `k` admits a guarded feedback
  witness for `g`.
* `fixedPointIndex g` — the least admissible closure/feedback weight (infimum of
  realizable budgets).
* `GuardedEnd.Le g h` — semantic domination preorder.
* `TraceConj g h` — trace-conjugacy under reversible equivalence.
* `GuardedEnd.comp g h` — stratified composition under oracle extension.
* `Eliminable g` — existence of a zero-cost representative in the same conjugacy class.
* `entropyBound` — an order-preserving entropy/complexity observable.
* `temporalFeedbackComplexity g` — the entropy bound applied to the fixed-point index.

## Main results

* `fixedPointIndex_eq_guardCost` — the infimum-based index equals the guard cost.
* `fixedPointIndex_least` — the index is the least realizable budget.
* `fixedPointIndex_mono` — monotonicity under enrichment order.
* `fixedPointIndex_traceConj_invariant` — invariance under trace-conjugacy.
* `fixedPointIndex_comp_eq` — exact additivity under stratified composition.
* `fixedPointIndex_zero_of_eliminable` — index zero for eliminable endomorphisms.
* `not_eliminable_of_pos_index` — nonzero index obstructs elimination.
* `entropy_monotone_of_monotone_map` — entropy monotonicity under monotone maps.
* `entropy_lower_bound_of_pos_index` — positive index forces positive entropy.
* `temporalFeedbackComplexity_lower_bound` — the central result: nonzero guarded
  fixed-point index forces nontrivial temporal feedback complexity.

## References

The conceptual framework connects:
- Lawvere's fixed-point theorem (categorical self-reference),
- traced monoidal categories (feedback semantics with quantitative weights),
- tropical/idempotent semiring methods (dequantization of complexity measures).

-/

open scoped ENNReal BigOperators

namespace GuardedFixedPointIndex

/-! ## Core Definitions -/

/-- A concrete guarded endomorphism carrying a morphism, an oracle level,
and a quantitative guard bound. The interpretation is that one application
of `f` must cross at least `guardCost` units of guarded delay / closure weight. -/
structure GuardedEnd (α : Type*) where
  /-- The underlying endofunction -/
  f : α → α
  /-- The oracle stratum at which this endomorphism operates -/
  oracleLevel : ℕ
  /-- The minimum guarded delay cost for one application -/
  guardCost : WithTop ℕ

/-- The realizability predicate: budget `k` admits a guarded feedback witness for `g`
when the guard cost is at most `k`. -/
def RealizesAt {α : Type*} (g : GuardedEnd α) (k : WithTop ℕ) : Prop :=
  g.guardCost ≤ k

/-- The guarded fixed-point index: the least admissible closure/feedback weight.
Defined as the infimum of all budgets that realize the guarded endomorphism. -/
noncomputable def fixedPointIndex {α : Type*} (g : GuardedEnd α) : WithTop ℕ :=
  sInf {k : WithTop ℕ | RealizesAt g k}

/-- Semantic domination preorder on guarded endomorphisms: `g` is dominated by `h`
when `h` operates at a higher or equal oracle level with higher or equal guard cost. -/
def GuardedEnd.Le {α : Type*} (g h : GuardedEnd α) : Prop :=
  g.oracleLevel ≤ h.oracleLevel ∧ g.guardCost ≤ h.guardCost

/-- Trace-conjugacy under reversible equivalence: two guarded endomorphisms are
trace-conjugate when they are related by a permutation conjugation that preserves
oracle level and guard cost. This captures the idea that the index depends only on
guarded feedback semantics, not on presentation. -/
def TraceConj {α : Type*} (g h : GuardedEnd α) : Prop :=
  ∃ e : Equiv.Perm α, h.f = e ∘ g.f ∘ e.symm ∧
    g.oracleLevel = h.oracleLevel ∧
    g.guardCost = h.guardCost

/-- Stratified composition of guarded endomorphisms under oracle extension.
The oracle level is the maximum of the two levels (both oracles are needed),
and the guard cost is additive (both guards must be crossed). -/
def GuardedEnd.comp {α : Type*} (g h : GuardedEnd α) : GuardedEnd α :=
  { f := g.f ∘ h.f
    oracleLevel := max g.oracleLevel h.oracleLevel
    guardCost := g.guardCost + h.guardCost }

/-- A guarded endomorphism is eliminable if there exists a zero-cost representative
in the same trace-conjugacy class. This means the guarded self-reference can be
removed without changing the semantic content. -/
def Eliminable {α : Type*} (g : GuardedEnd α) : Prop :=
  ∃ h : GuardedEnd α, TraceConj g h ∧ fixedPointIndex h = 0

/-- The entropy bound observable. In the concrete first version, this is the identity,
representing that entropy cost is at least the feedback weight. This can be replaced
by a more refined dequantization map when connecting to density-theoretic semantics. -/
def entropyBound : WithTop ℕ → WithTop ℕ := id

/-- The temporal feedback complexity of a guarded endomorphism: the entropy bound
applied to the fixed-point index. This is the central observable connecting
self-reference to computational cost. -/
noncomputable def temporalFeedbackComplexity {α : Type*} (g : GuardedEnd α) : WithTop ℕ :=
  entropyBound (fixedPointIndex g)

/-! ## Foundational Lemmas -/




/-! ## Index Characterization -/

/-
**Infimum characterization**: the fixed-point index equals the guard cost.
This is the fundamental identity connecting the infimum-based definition to
the concrete guard cost parameter.
-/

/-
**Least budget theorem**: the fixed-point index is realizable and is the
least realizable budget. This is the formal seed of the obstruction theory.
-/

/-
The fixed-point index is positive iff the guard cost is positive.
-/

/-! ## Monotonicity -/

/-
**Monotonicity under enrichment order**: if `g` is semantically dominated
by `h`, then the fixed-point index of `g` is at most that of `h`.
-/

/-
Monotonicity from oracle level and guard cost bounds.
-/

/-! ## Trace-Conjugacy Invariance -/

/-
Trace-conjugacy is reflexive.
-/

/-
Trace-conjugacy is symmetric.
-/

/-
**Invariance under trace-conjugacy**: the fixed-point index depends only on
the guarded feedback semantics, not on the presentation of the endomorphism.
-/

/-! ## Composition and Additivity -/

/-
The oracle level of a composition is the maximum of the component levels.
-/

/-
The guard cost of a composition is the sum of the component costs.
-/

/-
**Exact additivity**: the fixed-point index of a composition equals the sum
of the component indices. This reflects that stratified oracle extension requires
crossing both guards.
-/

/-
**Subadditivity** (follows from exact additivity).
-/

/-! ## Elimination Obstruction -/

/-
**Index zero for eliminable endomorphisms**: if a guarded endomorphism
is eliminable (has a zero-cost conjugate), then its own index is zero.
This follows from trace-conjugacy invariance.
-/

/-
**Obstruction theorem**: nonzero fixed-point index obstructs elimination.
This is the contrapositive of `fixedPointIndex_zero_of_eliminable` and is
the theorem that upgrades fixed-point semantics into a certificate of
irreducible feedback.
-/

/-
Nonzero guard cost implies non-eliminability.
-/

/-! ## Entropy Monotonicity -/

/-
**Entropy monotonicity under monotone maps**: any monotone observable
preserves the ordering of fixed-point indices.
-/

/-
**Entropy lower bound**: any monotone observable that is positive on
positive inputs gives a positive lower bound for positive-index endomorphisms.
-/

/-
The entropy bound is monotone.
-/

/-
The entropy bound preserves positivity.
-/

/-
**Central theorem**: nonzero guarded fixed-point index forces nontrivial
temporal feedback complexity. This is the main result connecting categorical
self-reference to computational lower bounds.
-/

end GuardedFixedPointIndex


