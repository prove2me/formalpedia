-- Prove2me | Definitions.Def_Geometry_CategoricalTower
-- name    : Geometry_CategoricalTower
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:52:57.240679+00:00
-- url     : https://prove2.me/theorems/3936579c-a819-476e-8b12-248b217df927
-- title:
--   Aether Catalog definitions — Geometry_CategoricalTower
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CategoricalTower`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CategoricalTower.lean by skeleton subtraction
import Mathlib
/-
  Categorical Tower Theory: Structural Theorems for Graded Hierarchies

  This file develops the theory of graded towers — sequences of finite types
  connected by transition maps — and studies how structural properties
  (injectivity, surjectivity, defect) propagate through the tower.

  The main results are:
  1. The Composition Injectivity Theorem: injective composition implies
     level-wise injectivity.
  2. The Anomaly-Range Duality: anomaly sets equal complements of ranges.
  3. The Shadow Filtration Theorem: shadow sets form a decreasing filtration.
  4. The Stability Monotonicity: stabilization propagates upward.
  5. Fiber-Defect Identity: fiber partition of unity.
  6. Injective-Surjective Collapse for finite types.
-/

open Finset Function

/-! ## Graded Towers -/

/-- A `GradedTower` is a sequence of types indexed by `Fin (n+1)` with transition
    maps between consecutive levels. This models a categorical hierarchy where
    each level maps to the next. -/
structure GradedTower (n : ℕ) where
  /-- The type at each level of the tower -/
  Level : Fin (n + 1) → Type
  /-- Transition map from level i to level i+1 -/
  transition : ∀ (i : Fin n), Level i.castSucc → Level i.succ

/-! ## Fiber and Anomaly Theory -/



/-- The anomaly set at level i is the complement of the range. -/
def GradedTower.anomalySet {n : ℕ} (t : GradedTower n)
    (i : Fin n) : Set (t.Level i.succ) :=
  (Set.range (t.transition i))ᶜ

/-
**Anomaly-Range Duality**: The anomaly set is exactly the complement of the range.
    This connects the "physics" language of anomalies with the "math" language of
    surjectivity, showing they encode identical information.
-/

/-
**Surjectivity-Anomaly Equivalence**: A transition map is surjective
    if and only if its anomaly set is empty.
-/

/-! ## Stability Theory -/

/-- A tower stabilizes at level k if all transitions from k onward are bijective. -/
def GradedTower.stabilizesAt {n : ℕ} (t : GradedTower n) (k : ℕ) : Prop :=
  ∀ i : Fin n, k ≤ i.val → Bijective (t.transition i)

/-
**Stability Monotonicity**: If a tower stabilizes at level j,
    it also stabilizes at any later level k ≥ j.
-/

/-! ## Shadow Sets and Filtration -/

/-- The shadow set at depth k from level i is the range of the composed map. -/
noncomputable def GradedTower.shadowAtOne {n : ℕ} (t : GradedTower n)
    (i : Fin n) : Set (t.Level i.succ) :=
  Set.range (t.transition i)

/-
**Shadow-Anomaly Partition**: The shadow set at depth 1 and the anomaly set
    partition the codomain level.
-/

/-
Shadow and anomaly sets are disjoint.
-/

/-! ## Core Cardinality Theorems -/

/-
**Injective implies card inequality**: If a function between finite types
    is injective, the domain has at most as many elements as the codomain.
    This is a standard result but serves as the base case for tower induction.
-/

/-
**Injective + equal card = surjective** for finite types.
-/

/-
**Bijective from injective + equal cardinality** for tower maps.
-/

/-
**Image cardinality for injective maps**: The image of an injective
    function has the same cardinality as the domain.
-/

/-! ## The (2,∞)-Necessity Theorem

In any tower where **every** transition map is bijective, the tower carries
no interesting structure — it is essentially a "trivial" tower where all
levels are isomorphic. For a tower to encode nontrivial physics, at least
one transition must fail to be bijective. We prove the stronger result that
a tower with at least two distinct cardinalities among its levels must have
at least two non-bijective transitions. -/

/-- A tower is *trivial* if every transition is bijective. -/
def GradedTower.isTrivial {n : ℕ} (t : GradedTower n) : Prop :=
  ∀ i : Fin n, Bijective (t.transition i)

/-
**Trivial towers have uniform cardinality**: If every transition is bijective,
    then all levels have the same cardinality. This is the structural rigidity
    theorem — bijective towers are "flat".
-/

/-
**Non-uniform implies nontrivial**: If two levels have different cardinalities,
    the tower must have at least one non-bijective transition between them.
-/

/-! ## Defect Theory -/

/-- The defect sequence measures card(codomain) - card(image) at each level. -/
noncomputable def GradedTower.defectSeq {n : ℕ} (t : GradedTower n)
    [∀ i, Fintype (t.Level i)] [∀ i, DecidableEq (t.Level i)]
    : Fin n → ℕ :=
  fun i => Fintype.card (t.Level i.succ) - Fintype.card (Set.range (t.transition i))

/-
**Zero defect iff surjective**: The defect at level i is zero if and only if
    the transition map is surjective. This connects the numerical defect
    invariant with the algebraic property.
-/

/-! ## Conjecture: Anomaly Cascade Converse

**Conjecture**: In a tower of height n ≥ 3, if the anomaly set is empty at
every level below k (all lower transitions are surjective), this does NOT
force the anomaly set at level k to be empty.

This is falsifiable: we can construct a concrete counterexample or prove
the implication holds. The conjecture predicts asymmetry in anomaly
propagation — anomalies are a "one-way" phenomenon.

**Test**: Construct a GradedTower 3 where transitions 0 and 1 are surjective
but transition 2 is not surjective. -/

/-- Witness tower showing anomaly cascade does NOT propagate upward:
    Lower surjectivity does not force upper surjectivity. -/
def anomalyCascadeCounterexample : GradedTower 2 where
  Level := fun i => match i with
    | ⟨0, _⟩ => Fin 3
    | ⟨1, _⟩ => Fin 3
    | ⟨2, _⟩ => Fin 4
  transition := fun i => match i with
    | ⟨0, _⟩ => fun x => x  -- identity: surjective
    | ⟨1, _⟩ => fun (x : Fin 3) => (⟨x.val, by omega⟩ : Fin 4)

/-
injection: not surjective

The first transition of the counterexample is surjective.
-/

/-
The second transition of the counterexample is NOT surjective.
-/


