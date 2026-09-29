-- Prove2me | Theorems.Thm_FundamentalGroupCompleteInvariant_aut_mulEquiv_of_groupoid_equivalence
-- name    : FundamentalGroupCompleteInvariant.aut_mulEquiv_of_groupoid_equivalence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:07.819417+00:00
-- url     : https://prove2.me/theorems/977e6770-d00a-415f-89fb-e64d9fb48173
-- title:
--   The converse: an equivalence of groupoids identifies automorphism groups at
-- statement:
--   The converse: an equivalence of groupoids identifies automorphism groups at
--   corresponding basepoints.
--
--   ```lean
--   theorem FundamentalGroupCompleteInvariant.aut_mulEquiv_of_groupoid_equivalence    {C : Type u} [Groupoid.{v} C] {D : Type u'} [Groupoid.{v'} D]
--       (E : C ≌ D) (c : C) : Nonempty (Aut c ≃* Aut (E.functor.obj c)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/FundamentalGroupCompleteInvariant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/FundamentalGroupCompleteInvariant.lean#L113

-- Thm stub generated from Bridges/FundamentalGroupCompleteInvariant.lean
import Mathlib
import Definitions.Def_Bridges_FundamentalGroupCompleteInvariant
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

open FundamentalGroupCompleteInvariant

universe u v u' v'



variable {C : Type u} [Groupoid.{v} C] (c : C)

theorem FundamentalGroupCompleteInvariant.aut_mulEquiv_of_groupoid_equivalence    {C : Type u} [Groupoid.{v} C] {D : Type u'} [Groupoid.{v'} D]
    (E : C ≌ D) (c : C) : Nonempty (Aut c ≃* Aut (E.functor.obj c)) := by sorry
