-- Prove2me | Theorems.Thm_SimpleGraph_Tree_eq_edgeTowardsOrigin_iff_of_mem
-- name    : SimpleGraph.Tree.eq_edgeTowardsOrigin_iff_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:12.861966+00:00
-- url     : https://prove2.me/theorems/535da47a-f96c-4ce4-b2d2-498df518e091
-- title:
--   Tree: eq edge Towards Origin iff of mem
-- statement:
--   The Tree construction uses the eq edge Towards Origin iff of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L411-L419
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L411-L419

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

theorem SimpleGraph.Tree.eq_edgeTowardsOrigin_iff_of_mem (w : V) (hw : 0 < X.dist v₀ w) (e : X.edgeSet)
    (hmem : w ∈ e.val) :
    e = X.edgeTowardsOrigin v₀ w hw ↔ X.target v₀ e = w := by sorry
