-- Prove2me | Theorems.Thm_SimpleGraph_Tree_outwardEdgeCone_nonempty_of_two_le_degree
-- name    : SimpleGraph.Tree.outwardEdgeCone_nonempty_of_two_le_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:15.013804+00:00
-- url     : https://prove2.me/theorems/8d799788-40c9-4dba-a6ab-75168a31c5df
-- title:
--   Tree: outward Edge Cone nonempty of two le degree
-- statement:
--   The Tree construction uses the outward Edge Cone nonempty of two le degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L437-L463
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L437-L463

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

theorem SimpleGraph.Tree.outwardEdgeCone_nonempty_of_two_le_degree {v : V} (hv : 2 ≤ X.degree v) :
    (X.outwardEdgeCone v₀ v).Nonempty := by sorry
