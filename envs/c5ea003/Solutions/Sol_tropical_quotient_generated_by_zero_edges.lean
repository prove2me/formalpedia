-- Prove2me | solution 1 for tropical_quotient_generated_by_zero_edges
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:10:04.267067+00:00
-- url     : https://prove2.me/submissions/3eb0e303-fe95-4e8d-9175-5fd522fd5f90

-- Sol generated from Logic/KnotAndBraidTheory/TropicalHoTT.lean
import Mathlib
import Definitions.Def_Logic_KnotAndBraidTheory_TropicalHoTT
/-
# Tropical Homotopy Type Theory: Idempotent Homotopy Semantics

This file develops a rigorous "tropical shadow" of identity and equivalence
from homotopy type theory, built on finite types, weighted relations, and
min-plus arithmetic.

## Main results

* `tropPathEq_isEquivalence`: The zero-distance relation on a tropical path
  space is an equivalence relation (Theorem 1).
* `TropEquiv.preserves_TropPathEq`: Tropical equivalences preserve path
  classes (Theorem 2).
* `matrixTropEquiv_decidable`: Tropical matrix equivalence is decidable
  (Theorem 3).
* `tropUnivalence_finite`: Classification theorem equating matrix-level
  and structure-level tropical equivalence (Tropical Univalence).
* Concrete examples on `Fin 3` and `Fin 4` distinguishing non-equivalent
  tropical types.
-/


open Finset Function

/-! ## Core Definitions -/






/-! ## Theorem 1: Tropical path zero relation is an equivalence relation -/

/-
The zero-distance relation on a tropical path space is an equivalence
    relation. This is the first bridge from identity types to tropical identity
    classes: the path type condenses into a computational quotient.
-/

/-! ## Theorem 2: Tropical equivalences preserve path classes -/

/-
A tropical equivalence induces a bijection on tropical path components.
    This is the tropical analogue of transport along equivalence: the bridge
    from path semantics to equivalence semantics.
-/

/-! ## Theorem 3: Decidability of matrix tropical equivalence -/

/-
For finite tropical path spaces, tropical equivalence is decidable:
    it reduces to searching over all permutations of `Fin n`. This is the
    tropical analogue of univalence becoming a decidable algebraic criterion.
-/

/-! ## Tropical Univalence: Classification theorem -/

/-
The tropical univalence theorem for finite spaces: matrix-level tropical
    equivalence coincides with structure-level tropical equivalence.
    Identity of structures up to equivalence becomes an explicit min-plus
    permutation witness.
-/

/-! ## Theorem 4: Zero-edge relation and tropical quotient -/


/-
Given a tropical path space, the zero-distance relation equals
    the equivalence closure of the zero-edge relation.

    This is the tropical shadow of a higher inductive quotient: constructors
    become weighted edges, path constructors become zero-cost identifications,
    and the resulting quotient is computable.
-/

/-! ## Concrete Examples -/

/-! ### Example A: Discrete metric on Fin 3 -/


/-
In the discrete space on Fin 3, two points are tropically path-equal
    iff they are equal.
-/

/-! ### Example B: Cyclic tropical circle on Fin 3 -/


/-! ### Example C: Distinguishing non-equivalent tropical types on Fin 4 -/



/-
The discrete and non-discrete Fin 4 metrics are not tropically equivalent:
    there is no permutation witness. This demonstrates that tropical univalence
    does NOT collapse all finite spaces of the same size.
-/

/-! ## Additional structural results -/



/-
Matrix tropical equivalence is reflexive.
-/

/-
Matrix tropical equivalence is symmetric.
-/

/-
Matrix tropical equivalence is transitive.
-/

/-
Matrix tropical equivalence is an equivalence relation.
-/

theorem solution    {α : Type*} [Fintype α] (X : TropicalPathSpace α) :
    TropPathEq X = Relation.EqvGen (ZeroEdgeRel X.d) := by
  funext x yropPathEq;
  nontriviality;
  simp_all +decide [ TropPathEq ];
  constructor <;> intro h;
  · exact Relation.EqvGen.rel _ _ h;
  · induction h;
    · assumption;
    · exact X.self _;
    · rw [ X.symm, ‹X.d _ _ = 0› ];
    · rename_i x y z hxy hyz hx hyhy;
      exact le_antisymm ( by simpa [ hx, hyhy ] using X.tri x y z ) ( Nat.zero_le _ )
