-- Prove2me | Theorems.Thm_SimpleGraph_Tree_incidenceFinset_eq_union
-- name    : SimpleGraph.Tree.incidenceFinset_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:29.45955+00:00
-- url     : https://prove2.me/theorems/ec602e21-5c42-4bb9-bef3-5ec416545d0e
-- title:
--   Tree: incidence Finset eq union
-- statement:
--   The Tree construction uses the incidence Finset eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L548-L577
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L548-L577

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
variable (n : ℕ) (g : X.edgeSet → M)

theorem SimpleGraph.Tree.incidenceFinset_eq_union (v : V) (hv : 0 < X.dist v₀ v) :
    X.incidenceFinset' v = { edgeTowardsOrigin v₀ v hv } ∪ X.outwardEdgeCone v₀ v := by sorry
