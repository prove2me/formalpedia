-- Prove2me | Theorems.Thm_SimpleGraph_Tree_vertex_mem_edgeTowardsOrigin
-- name    : SimpleGraph.Tree.vertex_mem_edgeTowardsOrigin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:15.925235+00:00
-- url     : https://prove2.me/theorems/7b68040f-61ce-4b96-87de-93d24fa14535
-- title:
--   Tree: vertex mem edge Towards Origin
-- statement:
--   The Tree construction uses the vertex mem edge Towards Origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L422-L425
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L422-L425

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
omit [(v : V) → Fintype ↑(X.neighborSet v)]

theorem SimpleGraph.Tree.vertex_mem_edgeTowardsOrigin (w : V) (hw : 0 < X.dist v₀ w) :
    w ∈ (edgeTowardsOrigin v₀ w hw).val := by sorry
