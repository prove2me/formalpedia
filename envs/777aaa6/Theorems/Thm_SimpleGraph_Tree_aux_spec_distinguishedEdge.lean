-- Prove2me | Theorems.Thm_SimpleGraph_Tree_aux_spec_distinguishedEdge
-- name    : SimpleGraph.Tree.aux_spec_distinguishedEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:53.753017+00:00
-- url     : https://prove2.me/theorems/70c204ee-d3d3-4df1-9c57-81ec1b56c6b6
-- title:
--   Tree: aux spec distinguished Edge
-- statement:
--   The Tree construction uses the aux spec distinguished Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L622-L655
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L622-L655

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

theorem SimpleGraph.Tree.aux_spec_distinguishedEdge (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n) (hlt : 0 < X.dist v₀ v)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    aux w f v₀ n (X.distinguishedEdge v₀ v hnonempty) =
      (w v)⁻¹ • f v - aux w f v₀ n (X.edgeTowardsOrigin v₀ v hlt) := by sorry
