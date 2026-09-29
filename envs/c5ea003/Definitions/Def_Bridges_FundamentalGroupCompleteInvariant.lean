-- Prove2me | Definitions.Def_Bridges_FundamentalGroupCompleteInvariant
-- name    : Bridges_FundamentalGroupCompleteInvariant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:37.492702+00:00
-- url     : https://prove2.me/theorems/013cc392-4bfb-4b05-858e-89a5397b8fbe
-- title:
--   Aether Catalog definitions — Bridges_FundamentalGroupCompleteInvariant
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FundamentalGroupCompleteInvariant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FundamentalGroupCompleteInvariant.lean by skeleton subtraction
import Mathlib
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
/-
# Fundamental groups classify connected homotopy 1-types

A connected groupoid is the algebraic model of a connected homotopy 1-type
(an Eilenberg--MacLane type `K(G,1)`).  This file proves that such a groupoid is
completely classified, up to equivalence, by the automorphism group of one
basepoint.  It also proves a topological counterexample showing why no analogous
classification holds for arbitrary spaces.
-/

open CategoryTheory
open scoped ContinuousMap

namespace FundamentalGroupCompleteInvariant

universe u v u' v'

/-- A pointed category is connected when every object is isomorphic to the basepoint.
For a fundamental groupoid this is the categorical form of path-connectedness. -/
def ConnectedAt (C : Type u) [Category.{v} C] (c : C) : Prop :=
  ∀ d : C, Nonempty (c ≅ d)

section ConnectedGroupoid

variable {C : Type u} [Groupoid.{v} C] (c : C)

/-- The canonical functor from the one-object category of the basepoint's
fundamental group into a connected groupoid. -/
noncomputable def vertexFunctor : SingleObj (Aut c) ⥤ C :=
  SingleObj.functor (Aut.toEnd c)

/-- The vertex functor is faithful. -/
theorem vertexFunctor_faithful : (vertexFunctor c).Faithful := by
  unfold vertexFunctor
  refine { map_injective := ?_ }
  intro _ _ f g hfg
  -- f g : Aut c, hfg : Aut.toEnd c f = Aut.toEnd c g
  simp only [SingleObj.functor_obj, SingleObj.functor_map] at hfg
  -- Aut c is Iso c c, and we need to show iso equality from hom equality
  exact Iso.ext hfg

/-- The vertex functor is full because every endomorphism in a groupoid is an
isomorphism. -/
theorem vertexFunctor_full : (vertexFunctor c).Full := by
  refine ⟨fun f => ⟨Iso.mk f (inv f) ?_ ?_, ?_⟩⟩
  · simp
  · simp
  · rfl

/-- Connectedness makes the vertex functor essentially surjective. -/
theorem vertexFunctor_essSurj (hC : ConnectedAt C c) :
    (vertexFunctor c).EssSurj := by
  refine ⟨ fun d => ?_ ⟩
  obtain ⟨iso⟩ := hC d
  exact ⟨ (), ⟨iso⟩ ⟩

/-- **Classification of connected groupoids by a vertex group.**
Every connected groupoid is equivalent to the one-object groupoid formed from
the automorphism group of any chosen object. -/
noncomputable def connectedGroupoidEquivSingleObj (hC : ConnectedAt C c) :
    C ≌ SingleObj (Aut c) := by
  letI : (vertexFunctor c).IsEquivalence :=
    { faithful := vertexFunctor_faithful c
      full := vertexFunctor_full c
      essSurj := vertexFunctor_essSurj c hC }
  exact (vertexFunctor c).asEquivalence.symm

end ConnectedGroupoid




section TopologicalConsequences

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]








end TopologicalConsequences

end FundamentalGroupCompleteInvariant


