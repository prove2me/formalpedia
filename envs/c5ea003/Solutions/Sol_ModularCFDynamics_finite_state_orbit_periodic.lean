-- Prove2me | solution 1 for ModularCFDynamics.finite_state_orbit_periodic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:18:57.536838+00:00
-- url     : https://prove2.me/submissions/e514e963-3f99-41b6-b9b0-c8594f2bb645

-- Sol generated from Bridges/GraphTheory/ModularCFDynamics.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_ModularCFDynamics
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Modular Continued-Fraction Dynamics and Periodicity Detection

## Overview

This file develops a theory connecting continued-fraction expansions to modular
dynamics, establishing that eventually periodic CF sequences produce eventually
periodic convergent sequences modulo any modulus, and that graph-theoretic
invariants built from these modular convergents inherit the periodicity.

## Main Definitions

- `CFState`: State of the CF convergent recurrence (p_{n-1}, p_n, q_{n-1}, q_n)
- `IsEventuallyPeriodic`: A sequence that becomes periodic after some index
- `ModularCFGraph`: Novel structure encoding the filtered graph built from
  convergents mod p
- `FilteredGraphSeq`: Sequence of graphs with periodicity properties

## Main Results

- `eventually_periodic_comp`: Composition preserves eventual periodicity
- `consecutive_pair_periodic`: Periodicity transfers through pair functions
- `transition_count_eventually_periodic`: Graph edge counts inherit periodicity
- `modular_cf_graph_vertex_bound`: Bounded vertex count for modular CF graphs
- `betti_periodic_of_edge_periodic`: Cross-domain bridge to topology
- `finite_state_orbit_periodic`: Pigeonhole-based orbit periodicity on finite types
-/

open Finset Function

open ModularCFDynamics

/-! ## §1. Eventually Periodic Sequences -/








/-! ## §2. Continued Fraction Convergent Recurrence -/







/-! ## §3. Modular CF Dynamics -/



/-! ## §4. Modular CF Graph (Novel Structure) -/





/-! ## §5. Periodicity Transfer Theorems -/



/-! ## §6. Pigeonhole-Based Finite Orbit Periodicity -/

/-
**Finite state orbit periodicity**: On a finite type, iterating any function
    produces an eventually periodic sequence.

    Proof by pigeonhole: among the first `card α + 1` iterates, two must be equal.
    This gives the cycle detection that powers the modular CF periodicity theorem.
-/

/-! ## §7. Cross-Domain Bridge: Graph Invariants → Barcode Periodicity -/





/-! ## §8. Concrete Examples -/





/-! ## §9. Full Pipeline Theorem -/


/-! ## §10. Falsifiable Conjecture -/



open ModularCFDynamics in
theorem solution{α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α) (x₀ : α) :
    ∃ N T, IsEventuallyPeriodic (fun n => F^[n] x₀) N T ∧
      N + T ≤ Fintype.card α := by
  by_contra h_no_cycle;
  -- By contradiction, assume there are no such $N$ and $T$.
  push_neg at h_no_cycle;
  -- By the pigeonhole principle, since there are only `Fintype �.card� α + 1` distinct elements in the sequence, two of them must be equal.
  obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : ℕ, i < j ∧ i ≤ Fintype.card α ∧ j ≤ Fintype.card α ∧ F^[i] x₀ = F^[j] x₀ := by
    by_contra h_no_cycle;
    exact absurd ( Finset.card_le_univ ( Finset.image ( fun n => F^[n] x₀ ) ( Finset.Iic ( Fintype.card α ) ) ) ) ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.mp fun hi' => h_no_cycle ⟨ j, i, hi', by aesop, by aesop, hij.symm ⟩ ) ( not_lt.mp fun hj' => h_no_cycle ⟨ i, j, hj', by aesop, by aesop, hij ⟩ ) ] ; simp +decide );
  have := h_no_cycle i ( j - i ) ?_ <;> simp_all +decide [ IsEventuallyPeriodic ];
  · omega;
  · intro n hn; induction hn <;> simp_all +decide [ Nat.succ_add, Function.iterate_succ_apply' ] ;
    rw [ Nat.add_sub_of_le hij.le ]
