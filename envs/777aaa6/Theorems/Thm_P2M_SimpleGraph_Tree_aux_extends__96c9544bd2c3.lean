-- Prove2me | Theorems.Thm_P2M_SimpleGraph_Tree_aux_extends__96c9544bd2c3
-- name    : P2M_SimpleGraph_Tree_aux_extends__96c9544bd2c3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:26.67548+00:00
-- url     : https://prove2.me/theorems/06037361-c279-4607-9c00-7ccb0c48b6d0
-- title:
--   P2 M Simple Graph Tree aux extends  96c9544bd2c3: P2 M Simple Graph Tree aux extends  96c9544bd2c3
-- statement:
--   The P2 M Simple Graph Tree aux extends  96c9544bd2c3 construction uses the P2 M Simple Graph Tree aux extends  96c9544bd2c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L530-L546
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L530-L546

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

theorem P2M_SimpleGraph_Tree_aux_extends__96c9544bd2c3 (n : ℕ) (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) ≤ n) :
    aux w f v₀ (X.dist v₀ (X.target v₀ e)) e = aux w f v₀ n e := by sorry

alias «SimpleGraph».«Tree».«aux_extends'» := P2M_SimpleGraph_Tree_aux_extends__96c9544bd2c3
