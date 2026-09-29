-- Prove2me | Definitions.Def_Bridges_TheoryMorphisms
-- name    : Bridges_TheoryMorphisms
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:05.394528+00:00
-- url     : https://prove2.me/theorems/bc1d31b6-b3ea-4d93-9c18-dded6175f40a
-- title:
--   Aether Catalog definitions — Bridges_TheoryMorphisms
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TheoryMorphisms`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TheoryMorphisms.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theory Morphisms: A Formal Framework for Cross-Domain Theorem Transfer

This file defines a minimal but powerful framework in which mathematical
theories become objects and structure-preserving maps (theory morphisms)
become arrows of a category. The key innovation is that morphisms carry
**monotonicity witnesses**: a morphism from theory T to theory U certifies
that every element's "invariant value" (complexity, depth, dimension, etc.)
can only increase under the translation.

## Main definitions

* `ResearchTheory` — a carrier type with a `ℕ`-valued invariant
* `TheoryHom T U` — a function `T.Carrier → U.Carrier` with a proof that
  it is monotone with respect to the theories' invariants
* `SatisfiesLowerBound T n` — existential witness that theory `T` achieves
  invariant value ≥ `n`

## Main results

* **Category laws**: identity, composition, associativity, unit laws
* **Depth monotonicity**: composed morphisms preserve and accumulate depth
* **Transfer principle**: lower-bound witnesses transport across morphisms
* **Catalog bridges**: concrete theory instances built from existing catalog
  theorems, with a certified cross-domain transfer

## Design notes

We model theories as `Type`-carrier + `ℕ`-valued invariant rather than
encoding first-order syntax. This pragmatic choice:
1. Avoids universe issues and syntax/semantics bureaucracy
2. Composes smoothly with Lean's type theory
3. Is expressive enough to capture the invariant-transfer content of
   catalog theorems (height bounds, split counts, capacity, stability)

The `ℕ`-valued invariant is the "common currency" enabling cross-domain
bridges. Real-valued or lattice-valued generalizations are natural
extensions (see FUTURE_DIRECTIONS.md).
-/


/-! ## §1. Core Definitions -/

/-- A **research theory** is a type equipped with a ℕ-valued invariant.
    The invariant measures complexity, depth, dimension, or any other
    quantitative certificate that we want to transport across domains. -/
structure ResearchTheory where
  /-- The carrier type of objects in this theory -/
  Carrier : Type
  /-- The invariant function measuring "depth" or "complexity" -/
  Inv : Carrier → ℕ

/-- A **theory morphism** from T to U is a function on carriers that
    is monotone with respect to the invariants: translating an object
    from T to U can only increase (or preserve) its certified depth. -/
structure TheoryHom (T U : ResearchTheory) where
  /-- The underlying function on carriers -/
  toFun : T.Carrier → U.Carrier
  /-- Monotonicity witness: depth cannot decrease under translation -/
  monotone_inv : ∀ x : T.Carrier, T.Inv x ≤ U.Inv (toFun x)

/-! ## §2. Category Structure -/


/-- The identity morphism on a theory. -/
def TheoryHom.id (T : ResearchTheory) : TheoryHom T T where
  toFun := _root_.id
  monotone_inv := fun _ => le_refl _

/-- Composition of theory morphisms. -/
def TheoryHom.comp {T U V : ResearchTheory}
    (f : TheoryHom T U) (g : TheoryHom U V) : TheoryHom T V where
  toFun := g.toFun ∘ f.toFun
  monotone_inv := fun x => le_trans (f.monotone_inv x) (g.monotone_inv (f.toFun x))




/-! ## §3. Depth Monotonicity Theorems -/




/-! ## §4. The Theorem Transfer Principle -/

/-- A theory **satisfies a lower bound** n if there exists an element
    whose invariant value is at least n. -/
def SatisfiesLowerBound (T : ResearchTheory) (n : ℕ) : Prop :=
  ∃ x : T.Carrier, n ≤ T.Inv x

/-
**Transfer principle**: if theory T achieves a lower bound n, and
    there is a morphism from T to U, then U also achieves that bound.
    This is the bridge theorem that turns the category into an engine
    for transporting existential research statements.
-/

/-
**Iterated transfer**: lower bounds survive arbitrary chains of
    morphism composition.
-/

/-! ## §5. Enriched Theory: Validity Predicates -/

/-- A **validated research theory** augments the basic theory with a
    validity predicate, enabling transfer of conditional results. -/
structure ValidatedTheory where
  Carrier : Type
  Complexity : Carrier → ℕ
  Valid : Carrier → Prop

/-- Morphism between validated theories: preserves validity and is
    complexity-monotone on valid elements. -/
structure ValidatedHom (T U : ValidatedTheory) where
  toFun : T.Carrier → U.Carrier
  map_valid : ∀ {x}, T.Valid x → U.Valid (toFun x)
  monotone_complexity : ∀ {x}, T.Valid x → T.Complexity x ≤ U.Complexity (toFun x)

/-- A validated theory **satisfies a conditional lower bound** if there
    exists a valid element achieving the bound. -/
def ValidatedSatisfiesLowerBound (T : ValidatedTheory) (n : ℕ) : Prop :=
  ∃ x : T.Carrier, T.Valid x ∧ n ≤ T.Complexity x

/-
**Validated transfer principle**: conditional lower bounds transfer
    through validated morphisms.
-/

/-! ## §6. Preorder Structure on Theories -/

/-- Theory T is **dominated** by theory U if there exists a morphism T → U.
    This defines a preorder on research theories. -/
def TheoryDominates (T U : ResearchTheory) : Prop :=
  Nonempty (TheoryHom T U)


/-
Domination is transitive.
-/

/-
If T dominates U, then any lower bound achieved by T is also
    achieved by U.
-/

/-! ## §7. Coproduct of Theories -/

/-- **Coproduct theory**: the coproduct uses the sum type with the
    natural invariant. -/
def ResearchTheory.coprod (T U : ResearchTheory) : ResearchTheory where
  Carrier := T.Carrier ⊕ U.Carrier
  Inv := fun s => match s with
    | Sum.inl x => T.Inv x
    | Sum.inr y => U.Inv y

/-- Left injection is a morphism. -/
def ResearchTheory.coprod_inl (T U : ResearchTheory) :
    TheoryHom T (T.coprod U) where
  toFun := Sum.inl
  monotone_inv := fun _ => le_refl _


/-
**Coproduct transfer**: lower bounds from either factor lift
    to the coproduct.
-/


/-! ## §8. Catalog Bridge Instances -/

/-- Simple height theory: carrier is ℕ (representing heights),
    invariant is the identity (height itself as complexity measure).
    This models the `key_dimension_lower_bound_from_height` catalog theorem,
    where height directly measures arithmetic complexity. -/
def HeightTheory : ResearchTheory where
  Carrier := ℕ
  Inv := _root_.id

/-- Cell theory: carrier is ℕ (representing cell-split parameters),
    invariant measures cell complexity as n*(n+1), modeling the
    `splitCount` growth from the `cell_split_bound_from_height` catalog
    theorem. The +1 ensures strict monotonicity over all ℕ. -/
def CellTheory : ResearchTheory where
  Carrier := ℕ
  Inv := fun n => n * (n + 1)

/-- Bridge morphism from height theory to cell theory:
    maps each height h to itself. The monotonicity h ≤ h*(h+1)
    holds for all h : ℕ since h*(h+1) ≥ h·1 = h. -/
def heightToCellMorphism : TheoryHom HeightTheory CellTheory where
  toFun := _root_.id
  monotone_inv := fun x => by
    simp only [HeightTheory, CellTheory, _root_.id]
    exact le_mul_of_one_le_right (Nat.zero_le x) (Nat.succ_le_succ (Nat.zero_le x))

/-- Capacity theory: carrier is ℕ (representing closure-class indices),
    invariant is the identity, modeling `cap_depends_on_closure_class`. -/
def CapacityTheory : ResearchTheory where
  Carrier := ℕ
  Inv := _root_.id

/-- Stability theory: carrier is ℕ (representing contraction iterates),
    invariant is the identity, modeling diagonal stability depth from
    `diagonal_stability_from_contraction`. -/
def StabilityTheory : ResearchTheory where
  Carrier := ℕ
  Inv := _root_.id

/-- Bridge: stability theory embeds into capacity theory.
    Models the insight that contraction-based stability certificates
    can be reinterpreted as closure-capacity certificates. -/
def stabilityToCapacity : TheoryHom StabilityTheory CapacityTheory where
  toFun := _root_.id
  monotone_inv := fun _ => le_refl _



/-- Dimension theory: a theory with shifted invariant n ↦ n + 1,
    suitable as an intermediate between height and stability theories. -/
def DimensionTheory : ResearchTheory where
  Carrier := ℕ
  Inv := fun n => n + 1

/-- Bridge: height theory to dimension theory.
    Height h maps to h, and h ≤ h + 1. -/
def heightToDimension : TheoryHom HeightTheory DimensionTheory where
  toFun := _root_.id
  monotone_inv := fun x => by
    simp only [HeightTheory, DimensionTheory, _root_.id]
    exact Nat.le_succ x

/-- Bridge: dimension theory to stability theory.
    Dimension n maps to n + 1, and (n+1) ≤ (n+1). -/
def dimensionToStability : TheoryHom DimensionTheory StabilityTheory where
  toFun := fun (n : ℕ) => n + 1
  monotone_inv := fun (x : ℕ) => by
    show x + 1 ≤ _root_.id (x + 1)
    rfl

/-- The composite height → stability pipeline. -/
def heightToStabilityPipeline : TheoryHom HeightTheory StabilityTheory :=
  TheoryHom.comp heightToDimension dimensionToStability



/-
**Strict depth increase**: the height → cell morphism strictly
    increases depth for heights ≥ 2.
-/

/-! ## §9. Functorial Properties -/

/-
**Morphism composition distributes over transfer**: transferring
    a bound through f;g gives the same result as transferring through
    the composite.
-/

/-! ## §10. Bounded Depth and Gap Theorem -/

/-- A theory has **bounded depth** n if every element has invariant ≤ n. -/
def HasBoundedDepth (T : ResearchTheory) (n : ℕ) : Prop :=
  ∀ x : T.Carrier, T.Inv x ≤ n

/-
**Contrapositive transfer**: if U has bounded depth n, then any
    theory with a morphism to U also has bounded depth n.
-/

/-
**Gap theorem**: if T achieves bound n+1 but U has bounded depth n,
    then there is no morphism from T to U.
-/


