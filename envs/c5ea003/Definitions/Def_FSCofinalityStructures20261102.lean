-- Prove2me | Definitions.Def_FSCofinalityStructures20261102
-- name    : FSCofinalityStructures20261102
-- status  : Definition
-- author  : @username
-- created : 2026-11-02T12:38:11.407698+00:00
-- url     : https://prove2.me/theorems/5f82b7ab-2b47-4932-a734-4fff42f72754
-- title:
--   Countable structure spaces, graph codes, and Borel reductions
-- statement:
--   A countable relational language has finitely many arguments at each symbol, including arity zero. Its structures on the natural numbers are their Boolean relation truth tables with the canonical product Borel sigma algebra. Isomorphism is witnessed by one permutation preserving every relation value. An invariant class is closed under this isomorphism. Simple undirected graphs have the corresponding concrete adjacency codes. Borel reductions are measurable maps preserving and reflecting the compared relations on every pair; no Borelness of either relation graph is built into the interface. A coded relation bundles its actual carrier, measurable space and predicate.
-- source:
--   Friedman--Stanley cofinality and Borel completeness: A proposed negative answer to the Friedman--Stanley question, supplied research draft dated 2 November 2026, FriedmanStanleyQuestion.tex, Section 2.1, Borel spaces and comparison; Section 2.2, countable structures; Theorem 1.2 setting.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Polish

set_option autoImplicit false
noncomputable section
open TopologicalSpace

namespace FSCofinality

/-- A countable relational language. Arity zero is allowed. -/
structure CountableRelationalLanguage where
  Symbol : Type
  arity : Symbol → ℕ
  countable : Countable Symbol

attribute [instance] CountableRelationalLanguage.countable

/-- An atomic relation coordinate on the fixed domain `ℕ`. -/
def Coordinate (L : CountableRelationalLanguage) :=
  Σ s : L.Symbol, Fin (L.arity s) → ℕ

instance (L : CountableRelationalLanguage) : Countable (Coordinate L) := by
  unfold Coordinate
  infer_instance

/-- All structures for `L` on `ℕ`, as their actual relation truth values. -/
def Structures (L : CountableRelationalLanguage) := Coordinate L → Bool

instance (L : CountableRelationalLanguage) : TopologicalSpace (Structures L) :=
  inferInstanceAs (TopologicalSpace (Coordinate L → Bool))

instance (L : CountableRelationalLanguage) : PolishSpace (Structures L) where
  toSecondCountableTopology :=
    inferInstanceAs (SecondCountableTopology (Coordinate L → Bool))
  toIsCompletelyMetrizableSpace :=
    inferInstanceAs (IsCompletelyMetrizableSpace (Coordinate L → Bool))

instance (L : CountableRelationalLanguage) : MeasurableSpace (Structures L) :=
  borel (Structures L)

instance (L : CountableRelationalLanguage) : BorelSpace (Structures L) := ⟨rfl⟩

/-- Isomorphism by one permutation of the fixed countable domain. -/
def Isomorphic {L : CountableRelationalLanguage} (M N : Structures L) : Prop :=
  ∃ e : ℕ ≃ ℕ, ∀ (s : L.Symbol) (a : Fin (L.arity s) → ℕ),
    M ⟨s,a⟩ = N ⟨s,e ∘ a⟩

def IsInvariant {L : CountableRelationalLanguage} (K : Set (Structures L)) : Prop :=
  ∀ {M N}, M ∈ K → Isomorphic M N → N ∈ K

def IsomorphismOn {L : CountableRelationalLanguage} (K : Set (Structures L))
    (M N : K) : Prop := Isomorphic M.val N.val

/-- Borel reduction: measurability and preservation and reflection on all pairs.
Neither input relation is required to have a Borel graph. -/
def BorelReducible {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y)

/-- A concrete measurable code space together with its classified relation.
The bundle deliberately imposes no Borelness hypothesis on the relation. -/
structure CodedRelation where
  Carrier : Type
  measurableSpace : MeasurableSpace Carrier
  rel : Carrier → Carrier → Prop

attribute [instance] CodedRelation.measurableSpace

def CodedRelation.Reduces (E F : CodedRelation) : Prop :=
  @BorelReducible E.Carrier F.Carrier E.measurableSpace F.measurableSpace E.rel F.rel

def classRelation (L : CountableRelationalLanguage) (K : Set (Structures L)) :
    CodedRelation where
  Carrier := K
  measurableSpace := inferInstance
  rel := IsomorphismOn K

/-- Truth tables of simple undirected graphs on `ℕ`. -/
def GraphCondition (g : ℕ × ℕ → Bool) : Prop :=
  (∀ n, g (n,n) = false) ∧ ∀ m n, g (m,n) = g (n,m)

def GraphSpace := {g : ℕ × ℕ → Bool // GraphCondition g}

instance : TopologicalSpace GraphSpace :=
  inferInstanceAs (TopologicalSpace {g : ℕ × ℕ → Bool // GraphCondition g})

instance : MeasurableSpace GraphSpace := borel GraphSpace
instance : BorelSpace GraphSpace := ⟨rfl⟩

theorem isClosed_graphCondition : IsClosed {g : ℕ × ℕ → Bool | GraphCondition g} := by
  have hd : IsClosed {g : ℕ × ℕ → Bool | ∀ n, g (n,n) = false} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun n => isClosed_eq (continuous_apply (n,n)) continuous_const)
  have hs : IsClosed {g : ℕ × ℕ → Bool | ∀ m n, g (m,n) = g (n,m)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun m => isClosed_iInter (fun n =>
      isClosed_eq (continuous_apply (m,n)) (continuous_apply (n,m))))
  exact hd.inter hs

instance : PolishSpace GraphSpace := by
  letI : PolishSpace (ℕ × ℕ → Bool) := {
    toSecondCountableTopology := inferInstance
    toIsCompletelyMetrizableSpace := inferInstance }
  exact isClosed_graphCondition.polishSpace

def GraphIsomorphic (g h : GraphSpace) : Prop :=
  ∃ e : ℕ ≃ ℕ, ∀ m n, g.val (m,n) = h.val (e m,e n)

def graphRelation : CodedRelation where
  Carrier := GraphSpace
  measurableSpace := inferInstance
  rel := GraphIsomorphic

end FSCofinality


