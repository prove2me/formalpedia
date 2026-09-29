-- Prove2me | solution 1 for ClosureGaugeRealization.chain_cl_eq_cl_singleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:07:44.658274+00:00
-- url     : https://prove2.me/submissions/a9261af7-471a-440d-a9fa-4b912d23074e

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
theorem solution(C : ClosureOp α) (hchain : ClosedSetsChain C)
    (S : Finset α) (hne : S.Nonempty) :
    ∃ s ∈ S, C.cl S = C.cl {s} := by
  -- By the chain property, the closures of the elements of S form a chain.
  have h_chain : ∀ s t : α, s ∈ S → t ∈ S → C.cl {s} ⊆ C.cl {t} ∨ C.cl {t} ⊆ C.cl {s} := by
    intros s t hs ht
    have h_closed : C.IsClosed (C.cl {s}) ∧ C.IsClosed (C.cl {t}) := by
      exact ⟨ C.idempotent _, C.idempotent _ ⟩;
    exact hchain _ _ h_closed.1 h_closed.2;
  obtain ⟨s, hs⟩ : ∃ s ∈ S, ∀ t ∈ S, C.cl {t} ⊆ C.cl {s} := by
    obtain ⟨s, hs⟩ : ∃ s ∈ S, ∀ t ∈ S, (C.cl {s}).card ≥ (C.cl {t}).card := by
      exact Finset.exists_max_image _ _ hne;
    refine' ⟨ s, hs.1, fun t ht => _ ⟩;
    cases h_chain s t hs.1 ht <;> simp_all +decide [ Finset.subset_iff ];
    have := Finset.eq_of_subset_of_card_le ‹_› ( by linarith [ hs.2 t ht ] ) ; aesop;
  refine' ⟨ s, hs.1, le_antisymm _ _ ⟩;
  · have h_subset : S ⊆ C.cl {s} := by
      exact fun x hx => hs.2 x hx ( C.extensive _ ( Finset.mem_singleton_self _ ) );
    exact C.monotone h_subset |> le_trans <| by simp +decide [ C.idempotent ] ;
  · exact C.monotone ( Finset.singleton_subset_iff.mpr hs.1 )
