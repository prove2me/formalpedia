-- Prove2me | Theorems.Thm_SimpleGraph_Tree_aux_spec_outwardEdgeCone_erase
-- name    : SimpleGraph.Tree.aux_spec_outwardEdgeCone_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:29.583521+00:00
-- url     : https://prove2.me/theorems/a58240bd-1d1c-4c1d-9a9a-778ecfc05e37
-- title:
--   Tree: aux spec outward Edge Cone erase
-- statement:
--   The Tree construction uses the aux spec outward Edge Cone erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L608-L620
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L608-L620

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

theorem SimpleGraph.Tree.aux_spec_outwardEdgeCone_erase (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    ∑ x ∈ (outwardEdgeCone v₀ v).erase (X.distinguishedEdge v₀ v hnonempty),
    aux w f v₀ n x = 0 := by sorry
