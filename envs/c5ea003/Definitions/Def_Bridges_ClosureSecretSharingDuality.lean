-- Prove2me | Definitions.Def_Bridges_ClosureSecretSharingDuality
-- name    : Bridges_ClosureSecretSharingDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:55.510804+00:00
-- url     : https://prove2.me/theorems/8dacbcd1-bf36-4489-9bde-1c6ba46d8ad1
-- title:
--   Aether Catalog definitions — Bridges_ClosureSecretSharingDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureSecretSharingDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureSecretSharingDuality.lean by skeleton subtraction
import Mathlib
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

/-- A closure operator on sets: extensive, monotone, idempotent. -/
structure IsClosureOperator {α : Type*} (cl : Set α → Set α) : Prop where
  extensive : ∀ A, A ⊆ cl A
  monotone : ∀ ⦃A B⦄, A ⊆ B → cl A ⊆ cl B
  idempotent : ∀ A, cl (cl A) = cl A

/-! ## §2 Lifting participants and authorization -/

/-- Lift a set of participants `S : Set X` to a set in `Option X`,
    mapping each `x ∈ S` to `some x`. The secret is `none`. -/
def liftParticipants {X : Type*} (S : Set X) : Set (Option X) :=
  {y | ∃ x ∈ S, y = some x}

/-- A set `S` of participants is *authorized* if the secret (`none`)
    lies in the closure of the lifted participant set. -/
def AuthorizedFromClosure {X : Type*}
    (cl : Set (Option X) → Set (Option X)) (S : Set X) : Prop :=
  none ∈ cl (liftParticipants S)

/-- A set `S` is *unauthorized* if the secret does not lie in the closure. -/
def UnauthorizedFromClosure {X : Type*}
    (cl : Set (Option X) → Set (Option X)) (S : Set X) : Prop :=
  none ∉ cl (liftParticipants S)

/-! ## §3 Monotonicity and complement lemmas -/




/-! ## §4 Minimal authorized sets and secret-circuits -/

/-- A set `S` is *minimal authorized* if it is authorized and no proper subset is. -/
def IsMinimalAuthorized {X : Type*}
    (A : Set X → Prop) (S : Set X) : Prop :=
  A S ∧ ∀ T, T ⊂ S → ¬ A T

/-- A set `S` is a *secret-circuit* if the secret is in the closure of `S`,
    but removing any single participant causes the secret to leave the closure. -/
def IsSecretCircuit {X : Type*}
    (cl : Set (Option X) → Set (Option X)) (S : Set X) : Prop :=
  none ∈ cl (liftParticipants S) ∧
  ∀ x ∈ S, none ∉ cl (liftParticipants (S \ {x}))

/-
**Theorem 2**: Minimal authorized sets are exactly the secret-circuits
    of the closure geometry.
-/

/-! ## §5 Pointed Dependency Systems -/

/-- A *pointed dependency system* over a participant type `X` consists of:
    - a carrier type with a span (closure) operation,
    - generator assignments for each participant,
    - a distinguished secret element,
    - axioms making span a closure operator with finite character. -/
structure PointedDependencySystem (X : Type u) where
  /-- The carrier type of the dependency system. -/
  Carrier : Type u
  /-- Span/closure operation on sets of carrier elements. -/
  span : Set Carrier → Set Carrier
  /-- Generator assignment: each participant maps to a carrier element. -/
  gen : X → Carrier
  /-- The secret element in the carrier. -/
  secret : Carrier
  /-- Span is extensive. -/
  span_extensive : ∀ A, A ⊆ span A
  /-- Span is monotone. -/
  span_mono : ∀ ⦃A B⦄, A ⊆ B → span A ⊆ span B
  /-- Span is idempotent. -/
  span_idem : ∀ A, span (span A) = span A

/-- Authorization via a dependency system: the secret is in the span of
    the images of the chosen participants. -/
def AuthorizedFromDependency {X : Type u}
    (D : PointedDependencySystem X) (S : Set X) : Prop :=
  D.secret ∈ D.span (D.gen '' S)


/-! ## §6 From Dependency Systems to Closure Operators -/

/-- Given a pointed dependency system, construct a closure operator on `Option X`
    by mapping `some x ↦ gen x` and `none ↦ secret`, then using span. -/
noncomputable def closureFromDependency {X : Type u}
    (D : PointedDependencySystem X) : Set (Option X) → Set (Option X) :=
  let toCarrier : Option X → D.Carrier := fun
    | some x => D.gen x
    | none => D.secret
  fun A => {y : Option X | toCarrier y ∈ D.span (toCarrier '' A)}

/-
The closure operator induced by a dependency system is indeed a closure operator.
-/

/-
**Theorem 3**: A dependency system's authorization agrees with the
    closure-based authorization from the induced closure operator.
-/

/-! ## §7 From Closure Operators to Dependency Systems -/

/-- Given a closure operator on `Option X`, construct a pointed dependency system
    with carrier `Option X` and span = cl. -/
def dependencyFromClosure {X : Type u}
    (cl : Set (Option X) → Set (Option X))
    (hcl : IsClosureOperator cl) : PointedDependencySystem X where
  Carrier := Option X
  span := cl
  gen := some
  secret := none
  span_extensive := hcl.extensive
  span_mono := hcl.monotone
  span_idem := hcl.idempotent

/-
**Theorem 4 (forward)**: The dependency system from a closure operator
    recovers the same authorization predicate.
-/

/-! ## §8 Closure-Exact Access Structures -/

/-- An access structure is *closure-exact* if it arises from some closure operator. -/
def ClosureExactAccessStructure {X : Type u} (A : Set X → Prop) : Prop :=
  ∃ cl : Set (Option X) → Set (Option X),
    IsClosureOperator cl ∧
    ∀ S : Set X, A S ↔ AuthorizedFromClosure cl S



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


