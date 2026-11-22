-- Prove2me | Theorems.Thm_P2M_SimpleGraph_Tree_aux_spec__aabb8af43f85
-- name    : P2M_SimpleGraph_Tree_aux_spec__aabb8af43f85
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:30.535628+00:00
-- url     : https://prove2.me/theorems/0846db48-d12a-4090-b176-bae21fac0393
-- title:
--   P2 M Simple Graph Tree aux spec  aabb8af43f85: P2 M Simple Graph Tree aux spec  aabb8af43f85
-- statement:
--   The P2 M Simple Graph Tree aux spec  aabb8af43f85 construction uses the P2 M Simple Graph Tree aux spec  aabb8af43f85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L584-L606
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L584-L606

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

theorem P2M_SimpleGraph_Tree_aux_spec__aabb8af43f85 (e : X.edgeSet) (n : ℕ) (he : X.dist v₀ (X.target v₀ e) ≤ n)
    (hnotdist : X.distinguishedEdge v₀ (X.source v₀ e)
        (outwardEdgeCone_nonempty_of_source v₀ e) ≠ e) :
    aux w f v₀ n e = 0 := by sorry

alias «SimpleGraph».«Tree».«aux_spec₀» := P2M_SimpleGraph_Tree_aux_spec__aabb8af43f85
