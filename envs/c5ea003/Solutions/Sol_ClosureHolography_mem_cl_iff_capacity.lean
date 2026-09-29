-- Prove2me | solution 1 for ClosureHolography.mem_cl_iff_capacity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:47.016406+00:00
-- url     : https://prove2.me/submissions/03842be7-91bf-4034-9aef-340cd8dfa0cc

-- Sol generated from Bridges/ClosureHolographyDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureHolographyDuality
/-
# Closure Holography Duality: Certified Boundary Reconstruction

This file formalizes a finite holography theorem for closure systems: bulk
dependency structure is completely encoded by boundary-visible capacity data,
with a certified minimal decoder recovering the bulk from the boundary.

## Main Results

* `FiniteClosureSystem` — Finite closure operator with extensivity, monotonicity, idempotence
* `BoundaryRankData` — Core rank function with monotonicity, closure invariance, faithfulness
* `closed_eq_of_rank_eq` — Faithfulness: equal rank on closed sets implies equal sets
* `cl_eq_of_rank_eq` — Equal rank implies equal closures
* `exists_minimal_generator` — Existence of minimum-cardinality generating set
* `holographicDecode` — Certified reconstruction algorithm
* `holographicDecode_correct` — Decoder produces cl(G) = cl(univ)
* `holographicDecode_minimal` — Decoder produces minimal generating set
* `mem_cl_iff_capacity` — Membership detection via capacity
* `holographic_duality` — Capacity profile determines the closure operator (the core duality)
* `admissible_rank_from_capacity` — Canonical rank data construction for separated systems
* `closure_holography_reconstruction` — Full reconstruction theorem
* `holographic_uniqueness` — Uniqueness up to closure isomorphism
* `finite_closure_holography_package` — Complete holography package

## Mathematical Significance

This is a finite algebraic analogue of holographic reconstruction (AdS/CFT):
- **Bulk** = closure system (dependency propagation)
- **Boundary** = capacity/rank profile (observable data)
- **Duality** = capacity profile determines the closure operator
- **Reconstruction** = minimal generator decoder with correctness certificate
- **Uniqueness** = any two systems with same boundary data are isomorphic

The key insight: `mem_cl_iff_capacity` shows that membership in the closure
can be detected purely from boundary capacity data, enabling full bulk
reconstruction from boundary observations.
-/


set_option maxHeartbeats 800000

open Finset

open ClosureHolography

variable {B : Type*} [Fintype B] [DecidableEq B]

/-! ## Section 1: Core Structures -/






/-! ## Section 2: Closure Capacity -/





/-! ## Section 3: Boundary Rank Data -/





/-! ## Section 4: Generator Candidates and Minimal Generators -/





/-! ## Section 5: Holographic Decoder -/




/-! ## Section 6: Membership Detection via Capacity -/


/-! ## Section 7: Holographic Duality — Capacity Determines Closure -/


/-! ## Section 8: Canonical Boundary Rank Data -/



/-! ## Section 9: Full Reconstruction Theorem -/


/-! ## Section 10: Closure Isomorphism and Uniqueness -/





/-! ## Section 11: Rank Profile Injectivity -/



/-! ## Section 12: Boundary Entanglement Rank -/




/-! ## Section 13: Capacity Supermodularity -/

/-
The closure capacity satisfies a supermodular-like inequality:
    `cap(X) + cap(Y) ≤ cap(X ∪ Y) + |cl(X) ∩ cl(Y)|`.
    This is dual to submodularity and reflects the "synergy" of closure.
-/

/-! ## Section 14: Complete Holography Package -/



open ClosureHolography in
theorem solution(C : FiniteClosureSystem B) (X : Finset B) (x : B) :
    x ∈ C.cl X ↔ closureCapacity C X = closureCapacity C (X ∪ {x}) := by
  constructor
  · intro hx
    have : C.cl (X ∪ {x}) = C.cl X := by
      apply Finset.Subset.antisymm
      · have : X ∪ {x} ⊆ C.cl X :=
          Finset.union_subset (C.extensive X) (Finset.singleton_subset_iff.mpr hx)
        calc C.cl (X ∪ {x}) ⊆ C.cl (C.cl X) := C.monotone this
          _ = C.cl X := C.idempotent X
      · exact C.monotone Finset.subset_union_left
    unfold closureCapacity; rw [this]
  · intro h
    have hsub : C.cl X ⊆ C.cl (X ∪ {x}) := C.monotone Finset.subset_union_left
    have heq : C.cl X = C.cl (X ∪ {x}) :=
      Finset.eq_of_subset_of_card_le hsub (by unfold closureCapacity at h; omega)
    have : x ∈ C.cl (X ∪ {x}) :=
      C.extensive _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rw [← heq] at this
    exact this
