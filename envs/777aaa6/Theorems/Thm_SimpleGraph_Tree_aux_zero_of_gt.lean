-- Prove2me | Theorems.Thm_SimpleGraph_Tree_aux_zero_of_gt
-- name    : SimpleGraph.Tree.aux_zero_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:39.300699+00:00
-- url     : https://prove2.me/theorems/a76f4827-a290-40ce-aaa1-0663fc7031bf
-- title:
--   Tree: aux zero of gt
-- statement:
--   The Tree construction uses the aux zero of gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L514-L521
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L514-L521

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

theorem SimpleGraph.Tree.aux_zero_of_gt (n : ℕ) (e : X.edgeSet) (h : n + 1 < X.dist v₀ (X.target v₀ e)) :
    aux w f v₀ n e = 0 := by sorry
