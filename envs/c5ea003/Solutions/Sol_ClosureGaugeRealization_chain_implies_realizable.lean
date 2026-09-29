-- Prove2me | solution 1 for ClosureGaugeRealization.chain_implies_realizable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:45.323893+00:00
-- url     : https://prove2.me/submissions/ea0d8f04-6051-4518-8b5f-98dbf4f175a4

-- Sol generated from Bridges/ClosureGaugeRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureGaugeRealizationDuality
import Theorems.Thm_ClosureGaugeRealization_chain_cl_eq_cl_singleton

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
theorem mem_cl_iff_singleton_subset (C : ClosureOp α) (S : Finset α) (x : α) :
    x ∈ C.cl S ↔ C.cl {x} ⊆ C.cl S := by
  constructor <;> intro h;
  · -- Since $x \in C.cl S$, we have $\{x\} \subseteq C.cl S$.
    have h_singleton_subset : {x} ⊆ C.cl S := by
      aesop;
    exact C.monotone h_singleton_subset |> Set.Subset.trans <| by simp +decide [ C.idempotent ] ;
  · exact h ( C.extensive _ ( Finset.mem_singleton_self _ ) )

/-
In a chain closure with nonempty S, cl(S) = cl{s} for some s ∈ S.
-/

/-
In a chain, subset ↔ card ≤ for closed sets.
-/
theorem chain_closed_subset_iff_card_le (C : ClosureOp α) (hchain : ClosedSetsChain C)
    (S T : Finset α) (hS : C.IsClosed S) (hT : C.IsClosed T) :
    S ⊆ T ↔ S.card ≤ T.card := by
  constructor <;> intro h;
  · exact Finset.card_le_card h;
  · have := hchain S T hS hT;
    cases this <;> simp_all +decide [ Finset.subset_iff ];
    have := Finset.eq_of_subset_of_card_le ‹_› ; aesop;

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
theorem solution(C : ClosureOp α) (hchain : ClosedSetsChain C) :
    GaugeRealizable C := by
  use fun x => (C.cl {x}).card - (C.cl ∅).card;
  ext S x; simp +decide [ mem_cl_iff_singleton_subset, valuationCl ] ;
  constructor;
  · by_cases hS : S.Nonempty;
    · obtain ⟨ s₀, hs₀ ⟩ := chain_cl_eq_cl_singleton C hchain S hS;
      intro hx
      have h_card : (C.cl {x}).card ≤ (C.cl {s₀}).card := by
        exact Finset.card_le_card ( hs₀.2 ▸ hx );
      have h_card_le : (C.cl {s₀}).card - (C.cl ∅).card ≤ S.sup (fun x => (C.cl {x}).card - (C.cl ∅).card) := by
        exact Finset.le_sup ( f := fun x => #(C.cl { x }) - #(C.cl ∅) ) hs₀.1;
      omega;
    · simp_all +decide [ Finset.not_nonempty_iff_eq_empty.mp hS ];
      exact fun h => Finset.card_le_card h;
  · by_cases hS : S.Nonempty;
    · intro hx
      obtain ⟨s₀, hs₀⟩ : ∃ s₀ ∈ S, (C.cl {x}).card - (C.cl ∅).card ≤ (C.cl {s₀}).card - (C.cl ∅).card := by
        contrapose! hx;
        have h_sup_lt : (S.sup (fun x => (C.cl {x}).card - (C.cl ∅).card)) < (C.cl {x}).card - (C.cl ∅).card := by
          grind +suggestions;
        exact lt_tsub_iff_right.mp h_sup_lt;
      have h_subset : C.cl {x} ⊆ C.cl {s₀} := by
        apply chain_closed_subset_iff_card_le C hchain (C.cl {x}) (C.cl {s₀}) (by
        exact C.idempotent _) (by
        exact C.idempotent _) |>.2;
        have h_card_le : (C.cl ∅).card ≤ (C.cl {x}).card ∧ (C.cl ∅).card ≤ (C.cl {s₀}).card := by
          exact ⟨ Finset.card_le_card ( C.monotone ( Finset.empty_subset _ ) ), Finset.card_le_card ( C.monotone ( Finset.empty_subset _ ) ) ⟩;
        omega;
      exact Finset.Subset.trans h_subset ( C.monotone ( Finset.singleton_subset_iff.mpr hs₀.1 ) );
    · intro h y hy; have := Finset.eq_of_subset_of_card_le ( show C.cl ∅ ⊆ C.cl { x } from C.monotone ( Finset.empty_subset _ ) ) ; aesop;
