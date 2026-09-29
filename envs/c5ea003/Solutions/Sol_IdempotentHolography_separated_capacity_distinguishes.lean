-- Prove2me | solution 1 for IdempotentHolography.separated_capacity_distinguishes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:15.508633+00:00
-- url     : https://prove2.me/submissions/02fa93aa-82c3-4a93-be9c-34b401ef6564

-- Sol generated from Bridges/IdempotentHolographicClosureDuality.lean
import Mathlib
import Definitions.Def_Bridges_IdempotentHolographicClosureDuality
/-
# Idempotent Holographic Closure Duality

This file formalizes a holographic reconstruction theorem for finitely generated
idempotent closure systems. The core result is that **boundary closure-capacity
data is a complete invariant of the bulk observable structure**, and that one can
reconstruct a canonical minimal bulk model from finite boundary tables.

## Main Results

* `holographic_duality` — Capacity profiles completely determine the closure operator
* `admissibleProfile_iff_realizable` — Characterization of realizable boundary profiles
* `reconstructBulk_correct` — Certified reconstruction algorithm
* `isClosed_iff_capacity_eq_card` — Closed sets detected by capacity = cardinality
* `closureEquiv_preserves_capacity` — Capacity invariance under closure equivalence
* `endomorphism_bijection` — Endomorphism recovery from capacity data
* `reconstructBulk_unique_full` — Full uniqueness of reconstruction

## Cross-Domain Connections

Uses `closure_lattice_certified_fixedpoint_capacity` from `ClosureLefschetzTrace`
and `quantum_thermodynamic_certified_capacity_invariant_under_closure_equiv`
from `ClosureMorita` as structural foundations.
-/


set_option maxHeartbeats 800000

open Finset Function

open IdempotentHolography

/-! ## Section 1: Core Structures — Closure Operators -/


variable {α : Type*} [Fintype α] [DecidableEq α]







/-! ## Section 2: Fundamental Capacity Properties -/







/-! ## Section 3: The Holographic Duality Theorem -/

/-
**Main Holographic Duality Theorem:**
    Equal capacity profiles force equal closure operators.
    The key insight: cl(s) is the unique closed set of size cap(s) containing s.
-/

/-! ## Section 4: Boundary Profiles -/



/-! ## Section 5: Admissibility and Realizability -/




/-! ## Section 6: Holographic Bulk Systems -/


instance (B : HoloBulk) : DecidableEq B.State := B.instDecEq





/-! ## Section 7: Reconstruction -/




/-! ## Section 8: Closure Equivalences and Capacity Invariance -/




/-! ## Section 9: Observable Endomorphisms -/








/-! ## Section 10: Closed Set Lattice Properties -/





/-! ## Section 11: Discrete and Trivial Closure Examples -/






/-! ## Section 12: Endomorphism Transport and Recovery -/





/-! ## Section 13: Full Reconstruction Theorem -/


/-! ## Section 14: Boundary Profile Injectivity -/


/-! ## Section 15: Tropical Submodularity

Note: Tropical submodularity (`cap(s ∪ t) + cap(s ∩ t) ≤ cap(s) + cap(t)`) does NOT hold
for arbitrary closure operators. Counterexample: on `Fin 6` with `cl({0}) = {0}`,
`cl({1}) = {1}`, `cl({0,1}) = Fin 6`, we get `cap({0,1}) + cap(∅) = 6 > 2 = cap({0}) + cap({1})`.

Submodularity is instead an *axiom* characterizing **admissible** boundary profiles—those
that arise from matroid-like or polymatroid closure systems. The holographic duality theorem
holds without submodularity; submodularity is an additional structural constraint for the
essential image characterization. -/

/-
The reverse inequality (supermodularity) always holds for closure capacity:
    `cap(s) + cap(t) ≤ cap(s ∪ t) + |cl s ∩ cl t|`.
-/

/-! ## Section 16: Separation Consequences -/

/-
In a separated system, singletons are distinguished by some capacity test.
-/

/-! ## Section 17: Capacity Determines Closed-Set Lattice -/


/-! ## Section 18: Fixedpoint Capacity Connection -/



/-! ## Section 19: Membership Detection -/

/-
x ∈ cl(s) iff cap(s) = cap(s ∪ {x}).
-/


open IdempotentHolography in
theorem solution(C : ClosureOp α)
    (hsep : ∀ a b : α, a ≠ b → C.cl {a} ≠ C.cl {b})
    (a b : α) (hab : a ≠ b) :
    ∃ s : Finset α, closureCapacity C (s ∪ {a}) ≠ closureCapacity C (s ∪ {b}) := by
  by_contra h;
  -- Consider $s = C.cl {b}$. We have $s ∪ {b} = C.cl {b}$ and $s ∪ {a} = C.cl {b} ∪ {a}$.
  set s := C.cl {b}
  have hs_b : s ∪ {b} = C.cl {b} := by
    exact Finset.union_eq_left.mpr ( C.extensive _ )
  have hs_a : s ∪ {a} = C.cl {b} ∪ {a} := by
    rfl;
  -- Since $C.cl {a} \neq C.cl {b}$, there exists an element $x \in C.cl {a}$ such that $x \notin C.cl {b}$.
  obtain ⟨x, hx_a, hx_b⟩ : ∃ x, x ∈ C.cl {a} ∧ x ∉ C.cl {b} := by
    exact Finset.not_subset.mp fun h' => hsep a b hab <| Finset.Subset.antisymm h' <| by
      simp_all +decide [ Finset.subset_iff, closureCapacity ];
      have := h ∅; simp_all +decide ;
      exact fun x hx => by have := Finset.eq_of_subset_of_card_le h' ( by linarith ) ; aesop;
  -- Since $x \in C.cl {a}$ and $x \notin C.cl {b}$, we have $x \in C.cl (s ∪ {a})$ but $x \notin C.cl (s ∪ {b})$.
  have hx_s_a : x ∈ C.cl (s ∪ {a}) := by
    exact C.monotone ( Finset.subset_union_right ) hx_a
  have hx_s_b : x ∉ C.cl (s ∪ {b}) := by
    grind +suggestions;
  refine' h ⟨ s, ne_of_gt ( Finset.card_lt_card _ ) ⟩;
  grind +suggestions
