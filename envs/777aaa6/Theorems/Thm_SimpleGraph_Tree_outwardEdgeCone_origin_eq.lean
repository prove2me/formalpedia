-- Prove2me | Theorems.Thm_SimpleGraph_Tree_outwardEdgeCone_origin_eq
-- name    : SimpleGraph.Tree.outwardEdgeCone_origin_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:48:17.172366+00:00
-- url     : https://prove2.me/theorems/294f2569-929b-4dc8-a3b4-6f6b49b89933
-- title:
--   Tree: outward Edge Cone origin eq
-- statement:
--   The outward edge cone of the origin `v₀` is the finset of all neighboring edges.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L270-L274
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L270-L274

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

theorem SimpleGraph.Tree.outwardEdgeCone_origin_eq : X.outwardEdgeCone v₀ v₀ = X.incidenceFinset' v₀ := by sorry
