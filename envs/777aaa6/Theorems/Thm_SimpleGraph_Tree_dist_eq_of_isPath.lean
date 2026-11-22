-- Prove2me | Theorems.Thm_SimpleGraph_Tree_dist_eq_of_isPath
-- name    : SimpleGraph.Tree.dist_eq_of_isPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:48:28.732171+00:00
-- url     : https://prove2.me/theorems/fd459162-c20c-42fb-8fd9-807d54e83fac
-- title:
--   Tree: dist eq of is Path
-- statement:
--   The Tree construction uses the dist eq of is Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L363-L367
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L363-L367

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
omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)]

theorem SimpleGraph.Tree.dist_eq_of_isPath {x y : V} (p : X.Walk x y) (hp : p.IsPath) :
    X.dist x y = p.length := by sorry
