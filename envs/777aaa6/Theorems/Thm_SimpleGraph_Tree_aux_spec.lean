-- Prove2me | Theorems.Thm_SimpleGraph_Tree_aux_spec
-- name    : SimpleGraph.Tree.aux_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:40.020833+00:00
-- url     : https://prove2.me/theorems/eff1b98b-e471-4b88-9478-5b1c312a7023
-- title:
--   Tree: aux spec
-- statement:
--   The Tree construction uses the aux spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L657-L699
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L657-L699

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

theorem SimpleGraph.Tree.aux_spec (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    w v • ∑ e ∈ X.incidenceFinset' v, aux w f v₀ n e = f v := by sorry
