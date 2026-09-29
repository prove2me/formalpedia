-- Prove2me | Definitions.Def_Logic_KnotAndBraidTheory_TropicalHoTT
-- name    : Logic_KnotAndBraidTheory_TropicalHoTT
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:06.527037+00:00
-- url     : https://prove2.me/theorems/0c6d48b0-7c10-4dba-935a-072e0ba31954
-- title:
--   Aether Catalog definitions — Logic_KnotAndBraidTheory_TropicalHoTT
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.KnotAndBraidTheory.TropicalHoTT`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/KnotAndBraidTheory/TropicalHoTT.lean by skeleton subtraction
import Mathlib
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

/-- A tropical path space on a finite type `α`: a pseudometric with ℕ-valued distances. -/
structure TropicalPathSpace (α : Type*) [Fintype α] where
  d : α → α → ℕ
  self : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  tri : ∀ x y z, d x z ≤ d x y + d y z

/-- The tropical path equality relation: two points are identified when their
    distance is zero. This is the tropical shadow of the identity type. -/
def TropPathEq {α : Type*} [Fintype α] (X : TropicalPathSpace α) : α → α → Prop :=
  fun x y => X.d x y = 0

/-- A tropical equivalence between two tropical path spaces: a bijection
    that preserves all pairwise distances. This is the tropical shadow of
    an equivalence of types. -/
structure TropEquiv (α β : Type*) [Fintype α] [Fintype β]
    (X : TropicalPathSpace α) (Y : TropicalPathSpace β) where
  toEquiv : α ≃ β
  isometry : ∀ x y, Y.d (toEquiv x) (toEquiv y) = X.d x y

/-- Distance matrix representation for finite tropical path spaces. -/
def DistanceMatrix (n : ℕ) := Fin n → Fin n → ℕ

/-- Matrix-level tropical equivalence: existence of a permutation witness. -/
def MatrixTropEquiv {n : ℕ} (D E : DistanceMatrix n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, E (σ i) (σ j) = D i j

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
instance matrixTropEquiv_decidable {n : ℕ} (D E : DistanceMatrix n) :
    Decidable (MatrixTropEquiv D E) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin n), ∀ i j, E (σ i) (σ j) = D i j))

/-! ## Tropical Univalence: Classification theorem -/

/-
The tropical univalence theorem for finite spaces: matrix-level tropical
    equivalence coincides with structure-level tropical equivalence.
    Identity of structures up to equivalence becomes an explicit min-plus
    permutation witness.
-/

/-! ## Theorem 4: Zero-edge relation and tropical quotient -/

/-- The zero-edge relation: two points are directly identified when the
    generating relation assigns zero weight. -/
def ZeroEdgeRel {α : Type*} (r : α → α → ℕ) : α → α → Prop :=
  fun x y => r x y = 0

/-
Given a tropical path space, the zero-distance relation equals
    the equivalence closure of the zero-edge relation.

    This is the tropical shadow of a higher inductive quotient: constructors
    become weighted edges, path constructors become zero-cost identifications,
    and the resulting quotient is computable.
-/

/-! ## Concrete Examples -/

/-! ### Example A: Discrete metric on Fin 3 -/

/-- The discrete tropical path space on `Fin 3`: distance 0 to self, distance 1
    to any other point. -/
def discreteFin3 : TropicalPathSpace (Fin 3) where
  d := fun i j => if i = j then 0 else 1
  self := fun x => if_pos rfl
  symm := fun x y => by
    show (if x = y then 0 else 1) = (if y = x then 0 else 1)
    split_ifs <;> simp_all [eq_comm]
  tri := fun x y z => by
    show (if x = z then 0 else 1) ≤ (if x = y then 0 else 1) + (if y = z then 0 else 1)
    split_ifs <;> simp_all

/-
In the discrete space on Fin 3, two points are tropically path-equal
    iff they are equal.
-/

/-! ### Example B: Cyclic tropical circle on Fin 3 -/


/-! ### Example C: Distinguishing non-equivalent tropical types on Fin 4 -/

/-- Distance matrix D on Fin 4: the discrete metric. -/
def exD4_discrete : DistanceMatrix 4 :=
  fun i j => if i = j then 0 else 1

/-- Distance matrix E on Fin 4: a non-discrete metric where some pairs
    have distance 2. -/
def exD4_nondiscrete : DistanceMatrix 4 :=
  fun i j =>
    if i = j then 0
    else if (i.val + j.val) % 2 = 0 then 2
    else 1

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


