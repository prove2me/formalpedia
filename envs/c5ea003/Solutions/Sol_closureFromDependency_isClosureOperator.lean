-- Prove2me | solution 1 for closureFromDependency_isClosureOperator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:04:26.778575+00:00
-- url     : https://prove2.me/submissions/43914234-70fe-4fb6-8f65-692da2bb0953

-- Sol generated from Bridges/ClosureSecretSharingDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureSecretSharingDuality
/-
# Closure–Secret-Sharing Duality via Idempotent Dependency Systems

This module establishes a formal duality between:
- **Finite monotone access structures** (the cryptographic side),
- **Closure operators on pointed participant sets** (the geometric side),
- **Pointed dependency systems** (the algebraic side).

The main results:
1. Authorization induced by a closure operator is monotone (upward-closed).
2. Minimal authorized sets are exactly the "secret-circuits" of the closure geometry.
3. Every pointed dependency system induces a closure-exact access structure.
4. Every closure-exact access structure admits a pointed dependency representation.
5. Certified enumeration of minimal authorized sets.

## Key Insight

A secret-sharing access structure is not just *representable* by closure data —
it *is* a pointed closure geometry. Authorization means "the secret lies in the
span of the chosen participants," and unauthorized sets are exactly the flats
avoiding the secret.
-/


open Set Function

universe u

/-! ## §1 Closure Operators -/


/-! ## §2 Lifting participants and authorization -/




/-! ## §3 Monotonicity and complement lemmas -/




/-! ## §4 Minimal authorized sets and secret-circuits -/



/-
**Theorem 2**: Minimal authorized sets are exactly the secret-circuits
    of the closure geometry.
-/

/-! ## §5 Pointed Dependency Systems -/




/-! ## §6 From Dependency Systems to Closure Operators -/


/-
The closure operator induced by a dependency system is indeed a closure operator.
-/

/-
**Theorem 3**: A dependency system's authorization agrees with the
    closure-based authorization from the induced closure operator.
-/

/-! ## §7 From Closure Operators to Dependency Systems -/


/-
**Theorem 4 (forward)**: The dependency system from a closure operator
    recovers the same authorization predicate.
-/

/-! ## §8 Closure-Exact Access Structures -/




/-! ## §9 Round-trip: closure → dependency → closure preserves authorization -/

/-
The round-trip closure → dependency → closure recovers the original authorization.
-/

/-
The round-trip dependency → closure → dependency recovers the original authorization.
-/

/-! ## §10 Minimal authorized sets: finitary structure -/

/-
Every authorized set in a closure-exact access structure contains
    a minimal authorized subset (finite case).
-/

/-! ## §11 Irredundant presentations -/



/-! ## §12 Summary: the main duality theorem -/


theorem solution{X : Type u}
    (D : PointedDependencySystem X) :
    IsClosureOperator (closureFromDependency D) := by
  constructor <;> simp +decide [ closureFromDependency ];
  · exact fun A x hx => D.span_extensive _ <| Set.mem_image_of_mem _ hx;
  · exact fun A B hAB a ha => D.span_mono ( Set.image_mono hAB ) ha;
  · intro A;
    ext y;
    constructor <;> intro hy;
    · refine' D.span_idem _ ▸ _;
      refine' D.span_mono _ hy;
      exact Set.image_subset_iff.mpr fun x hx => hx;
    · refine' D.span_extensive _ _;
      exact ⟨ y, hy, rfl ⟩
