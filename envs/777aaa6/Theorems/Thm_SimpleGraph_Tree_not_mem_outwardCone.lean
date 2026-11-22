-- Prove2me | Theorems.Thm_SimpleGraph_Tree_not_mem_outwardCone
-- name    : SimpleGraph.Tree.not_mem_outwardCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:59:11.215597+00:00
-- url     : https://prove2.me/theorems/5b37d7cc-009d-4b61-884e-b97d6132c337
-- title:
--   Tree: not mem outward Cone
-- statement:
--   The Tree construction uses the not mem outward Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L244-L245
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L244-L245

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
omit [DecidableEq V]

theorem SimpleGraph.Tree.not_mem_outwardCone (w : V) : w ∉ X.outwardCone v₀ w := by sorry
