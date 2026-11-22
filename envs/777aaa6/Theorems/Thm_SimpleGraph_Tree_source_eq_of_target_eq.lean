-- Prove2me | Theorems.Thm_SimpleGraph_Tree_source_eq_of_target_eq
-- name    : SimpleGraph.Tree.source_eq_of_target_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:00.501115+00:00
-- url     : https://prove2.me/theorems/efef442c-64cb-4a3a-9883-02a0d05570c4
-- title:
--   Tree: source eq of target eq
-- statement:
--   The Tree construction uses the source eq of target eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L370-L403
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L370-L403

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
omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)]

theorem SimpleGraph.Tree.source_eq_of_target_eq (e f : X.edgeSet) (h : X.target v₀ e = X.target v₀ f) :
    X.source v₀ e = X.source v₀ f := by sorry
