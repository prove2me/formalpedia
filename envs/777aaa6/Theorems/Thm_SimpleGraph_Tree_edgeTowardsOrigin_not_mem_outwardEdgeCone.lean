-- Prove2me | Theorems.Thm_SimpleGraph_Tree_edgeTowardsOrigin_not_mem_outwardEdgeCone
-- name    : SimpleGraph.Tree.edgeTowardsOrigin_not_mem_outwardEdgeCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:14.992861+00:00
-- url     : https://prove2.me/theorems/570c1930-99b5-40db-8817-2c5a64edf76b
-- title:
--   Tree: edge Towards Origin not mem outward Edge Cone
-- statement:
--   The Tree construction uses the edge Towards Origin not mem outward Edge Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L427-L435
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L427-L435

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

theorem SimpleGraph.Tree.edgeTowardsOrigin_not_mem_outwardEdgeCone (v : V) (hdist : 0 < X.dist v₀ v) :
    edgeTowardsOrigin v₀ v hdist ∉ outwardEdgeCone v₀ v := by sorry
