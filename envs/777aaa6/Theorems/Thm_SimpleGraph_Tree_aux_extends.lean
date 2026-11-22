-- Prove2me | Theorems.Thm_SimpleGraph_Tree_aux_extends
-- name    : SimpleGraph.Tree.aux_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:35.146743+00:00
-- url     : https://prove2.me/theorems/b93c693a-15db-4ae0-a03d-d9d83285d4d3
-- title:
--   Tree: aux extends
-- statement:
--   The Tree construction uses the aux extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L523-L528
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L523-L528

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

theorem SimpleGraph.Tree.aux_extends (n : ℕ) (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) ≤ n) :
    aux w f v₀ (n + 1) e = aux w f v₀ n e := by sorry
