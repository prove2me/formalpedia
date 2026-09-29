-- Prove2me | Definitions.Def_Logic_CategoryDNA
-- name    : Logic_CategoryDNA
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:48:50.096472+00:00
-- url     : https://prove2.me/theorems/c580064f-d6a4-4e2b-9cc9-5e4b5dbb0894
-- title:
--   Aether Catalog definitions — Logic_CategoryDNA
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.CategoryDNA`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/CategoryDNA.lean by skeleton subtraction
import Mathlib
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Category theory as a precise “genome” metaphor

We test the proposed slogans on a deliberately broad class of theories: a theory is
represented only by its type of models, and its genome is the discrete category on
those models.  This setting is broad enough to prove an exact Morita theorem and to
exhibit an obstruction to the proposed mutation principle.
-/

universe u v

open CategoryTheory

namespace CategoryDNA

/-- A minimal semantic theory, retaining its collection of models. -/
structure Theory where
  Model : Type u

/-- The genome of a theory is its category of models. -/
abbrev Theory.Genome (T : Theory.{u}) := Discrete T.Model

/-- Semantic Morita equivalence at the level of model types. -/
def MoritaEquivalent (T U : Theory.{u}) : Prop := Nonempty (T.Model ≃ U.Model)

/-- Morita equivalence expressed categorically at the level of genomes. -/
def CategoricallyMoritaEquivalent (T U : Theory.{u}) : Prop :=
  Nonempty (T.Genome ≌ U.Genome)

/-
For discrete model semantics, type-level and categorical Morita equivalence agree exactly.
-/

/-
Morita equivalences compose, corresponding to composition of genome equivalences.
-/

/-- Strengthening a theory by one axiom `P` restricts models to a subtype. -/
def axiomMutation (T : Theory.{u}) (P : T.Model → Prop) : Theory.{u} :=
  ⟨Subtype P⟩

/-- The forgetful functor from models satisfying a new axiom to old models. -/
def mutationForgetful (T : Theory.{u}) (P : T.Model → Prop) :
    (axiomMutation T P).Genome ⥤ T.Genome :=
  Discrete.functor (fun X => Discrete.mk X.val)

/-
A right adjoint to axiom-forgetting forces the new axiom to hold in every old model.
This is the key obstruction to the unrestricted mutation slogan.
-/

/-
Conversely, a redundant axiom does produce an adjunction: the forgetful functor is
part of an equivalence of discrete model categories.
-/

/-
Complete classification: in discrete semantics, adjoining one axiom has the claimed
right adjoint exactly when the axiom was already valid in every model.
-/

/-
Concrete counterexample to “every one-axiom mutation induces an adjunction”.
Starting with one model and adjoining the false axiom leaves no models.
-/

/-
A conservative evolutionary path (an equivalence of genomes) is a single
adjunction step.  Thus the path-decomposition conjecture is valid for equivalences,
but the counterexample above shows it fails for arbitrary axiom changes.
-/

end CategoryDNA


