-- Prove2me | Theorems.Thm_SimpleGraph_Tree_mem_outwardCone_iff
-- name    : SimpleGraph.Tree.mem_outwardCone_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:48:06.430859+00:00
-- url     : https://prove2.me/theorems/dfa0d44c-9149-4904-a6de-424f4b4e616b
-- title:
--   Tree: mem outward Cone iff
-- statement:
--   A vertex `a` is in the outward cone of a vertex `w`, iff `a` is a neighbour and has
--   bigger distance to `v₀` than `w`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L239-L241
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L239-L241

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

theorem SimpleGraph.Tree.mem_outwardCone_iff (w a : V) :
    a ∈ X.outwardCone v₀ w ↔ (X.Adj w a ∧ X.dist v₀ w < X.dist v₀ a) := by sorry
