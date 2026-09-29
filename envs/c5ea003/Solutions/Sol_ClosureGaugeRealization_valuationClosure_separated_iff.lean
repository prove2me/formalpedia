-- Prove2me | solution 1 for ClosureGaugeRealization.valuationClosure_separated_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:46.499981+00:00
-- url     : https://prove2.me/submissions/506d3cfa-c408-4e63-9111-a78ddb265abe

-- Sol generated from Bridges/ClosureGaugeRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureGaugeRealizationDuality

/-!
# Closure–Gauge Realization Duality via Idempotent Holonomy

This file establishes a finite realization/minimality duality for discrete gauge fields
encoded by closure data. It builds a formal bridge between:

- **Closure systems** from lattice theory and EML
- **Idempotent/tropical linear algebra** (valuations in ℕ with max/sup)
- **Automata-theoretic finite realization** (Hankel/Nerode style)
- **Discrete gauge theory / lattice holonomy** (Wilson-loop observables)

## Core Idea

A *gauge valuation* assigns a non-negative integer "holonomy capacity" to each element
(abstracting: loop ↦ holonomy value). The *induced closure* captures all elements
whose capacity is dominated by the supremum of a given set:

  `cl_v(S) = { x | v(x) ≤ sup_{s ∈ S} v(s) }`

## Main Results

* `valuationClosure` — Valuation-induced closure is a closure operator
* `valuationClosure_closedSets_chain` — Closed sets form a chain
* `valuationClosure_eq_iff_orderEquiv` — Equal closures ↔ order-equivalent valuations
* `closureOp_realizable_iff_chain` — Realizability iff closed sets form a chain
* `minimal_realization_exists` — Existence of minimal realization
* `minimal_realizations_orderEquiv` — Uniqueness up to gauge equivalence
* `certified_reconstruction` — Certified reconstruction from chain decomposition
-/

set_option maxHeartbeats 800000

open Finset Function

open ClosureGaugeRealization

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Section 1: Closure Operators -/



/-! ## Section 2: Gauge Valuations and Induced Closure -/





/-
Key lemma: the sup of a valuation closure equals the sup of the original set.
-/

/-
The valuation closure is idempotent: `cl_v(cl_v(S)) = cl_v(S)`.
-/


/-! ## Section 3: Closed Sets of Valuation Closures Form a Chain -/

/-
A closed set of the valuation closure is exactly a level set `{x | v(x) ≤ k}`
    for `k = S.sup v`.
-/

/-
Two closed sets of a valuation closure are comparable under inclusion.
-/

/-! ## Section 4: Order Equivalence (Gauge Equivalence) -/





/-
**Fundamental Gauge Uniqueness**: Equal valuation closures imply
    order-equivalent valuations (gauge equivalence).
    Key idea: `v₁(x) ≤ v₁(y) ↔ x ∈ cl_{v₁}({y}) ↔ x ∈ cl_{v₂}({y}) ↔ v₂(x) ≤ v₂(y)`.
-/

/-! ## Section 5: Capacity and Holographic Duality -/




/-
A set is closed iff capacity equals cardinality.
-/

/-
**Holographic duality**: Equal capacity profiles imply equal closures.
-/

/-! ## Section 6: Realizability -/




/-
Forward direction: realizable implies chain.
-/

/-
Key helper: x ∈ cl(S) iff cl{x} ⊆ cl(S).
-/

/-
In a chain closure with nonempty S, cl(S) = cl{s} for some s ∈ S.
-/

/-
In a chain, subset ↔ card ≤ for closed sets.
-/

/-
Backward direction: chain implies realizable.
    Construction: v(x) = (cl{x}).card - (cl ∅).card.
-/


/-! ## Section 7: Realization Rank and Minimality -/




/-
The normalized valuation is order-equivalent to the original.
-/

/-
**Existence of minimal realization**.
-/

/-! ## Section 8: Uniqueness Up to Gauge Equivalence -/

/-
**Uniqueness**: Any two minimal realizations of the same closure
    are order-equivalent (gauge-equivalent).
-/

/-! ## Section 9: Certified Reconstruction -/

/-
**Certified reconstruction**: Given a closure with chain closed sets,
    one can reconstruct a minimal gauge valuation realizing it.
-/

/-! ## Section 10: The Main Duality Theorem -/


/-! ## Section 11: Concrete Examples -/

/-
The discrete closure (identity) is NOT gauge-realizable for n ≥ 2,
    since the identity closure has non-chain closed sets.
-/


/-
The total closure (everything maps to univ) is gauge-realizable.
-/

/-! ## Section 12: Separation and Injectivity -/

/-
In a valuation closure, separation ↔ injectivity of the valuation.
-/

/-
Separated closures with chain property admit injective realizations.
-/


open ClosureGaugeRealization in
theorem solution(v : α → ℕ) :
    Separated (valuationClosure v) ↔ Function.Injective v := by
  constructor;
  · intro h_inj v w hvw;
    contrapose! h_inj;
    unfold Separated; simp +decide;
    refine' ⟨ v, w, h_inj, _ ⟩;
    ext x; simp [valuationClosure];
    unfold valuationCl; aesop;
  · intro hv a b hab;
    simp_all +decide [ Finset.ext_iff, valuationClosure ];
    cases lt_or_gt_of_ne ( hv.ne hab ) <;> simp_all +decide [ valuationCl ];
    · exact ⟨ b, by aesop ⟩;
    · exact ⟨ a, by aesop ⟩
