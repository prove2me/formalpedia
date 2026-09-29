-- Prove2me | Theorems.Thm_FundamentalGroupCompleteInvariant_connectedGroupoids_equivalent_of_aut_mulEquiv
-- name    : FundamentalGroupCompleteInvariant.connectedGroupoids_equivalent_of_aut_mulEquiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:17.680853+00:00
-- url     : https://prove2.me/theorems/3eb8da88-5868-4f25-8526-eed89ab92811
-- title:
--   Complete-invariant theorem for connected homotopy 1-types.
-- statement:
--   **Complete-invariant theorem for connected homotopy 1-types.**
--   Two connected groupoids whose fundamental groups at chosen basepoints are
--   isomorphic are equivalent categories.  Under the groupoid model of homotopy
--   1-types, this is precisely the statement that `K(G,1)` spaces are classified by
--   `G` up to isomorphism.
--
--   ```lean
--   theorem FundamentalGroupCompleteInvariant.connectedGroupoids_equivalent_of_aut_mulEquiv    {C : Type u} [Groupoid.{v} C] {D : Type u'} [Groupoid.{v'} D]
--       (c : C) (d : D) (hC : ConnectedAt C c) (hD : ConnectedAt D d)
--       (e : Aut c ≃* Aut d) : Nonempty (C ≌ D) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/FundamentalGroupCompleteInvariant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/FundamentalGroupCompleteInvariant.lean#L72

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

theorem FundamentalGroupCompleteInvariant.connectedGroupoids_equivalent_of_aut_mulEquiv    {C : Type u} [Groupoid.{v} C] {D : Type u'} [Groupoid.{v'} D]
    (c : C) (d : D) (hC : ConnectedAt C c) (hD : ConnectedAt D d)
    (e : Aut c ≃* Aut d) : Nonempty (C ≌ D) := by sorry
