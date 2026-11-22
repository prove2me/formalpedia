-- Prove2me | Theorems.Thm_SimpleGraph_Tree_outwardEdgeCone_eq_union
-- name    : SimpleGraph.Tree.outwardEdgeCone_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:59:25.14021+00:00
-- url     : https://prove2.me/theorems/04aab0a1-2ffb-44e9-94a0-74504c5732f3
-- title:
--   Tree: outward Edge Cone eq union
-- statement:
--   The Tree construction uses the outward Edge Cone eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L291-L303
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L291-L303

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
open SimpleGraph.Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)

theorem SimpleGraph.Tree.outwardEdgeCone_eq_union (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) :
    X.outwardEdgeCone v₀ w = { X.distinguishedEdge v₀ w hw } ∪
        { e | e ∈ X.outwardEdgeCone v₀ w ∧ X.distinguishedEdge v₀ w hw ≠ e } := by sorry
