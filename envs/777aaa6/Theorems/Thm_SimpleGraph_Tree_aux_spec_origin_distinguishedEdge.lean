-- Prove2me | Theorems.Thm_SimpleGraph_Tree_aux_spec_origin_distinguishedEdge
-- name    : SimpleGraph.Tree.aux_spec_origin_distinguishedEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:40.983387+00:00
-- url     : https://prove2.me/theorems/08ca4bae-9273-4766-868d-6d348777eea3
-- title:
--   Tree: aux spec origin distinguished Edge
-- statement:
--   The Tree construction uses the aux spec origin distinguished Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L579-L582
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L579-L582

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

theorem SimpleGraph.Tree.aux_spec_origin_distinguishedEdge (hnonempty : (X.outwardEdgeCone v₀ v₀).Nonempty) :
    aux w f v₀ 1 (distinguishedEdge v₀ v₀ hnonempty) = (w v₀)⁻¹ • f v₀ := by sorry
