-- Prove2me | Theorems.Thm_SimpleGraph_Tree_laplace_preimage
-- name    : SimpleGraph.Tree.laplace_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:41.990937+00:00
-- url     : https://prove2.me/theorems/b312e019-c4b9-4ff3-a618-a01fa05bf375
-- title:
--   Tree: laplace preimage
-- statement:
--   The constructed preimage is indeed a preimage of the Laplacian.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L705-L723
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L705-L723

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

theorem SimpleGraph.Tree.laplace_preimage (hinfinite : ∀ v, (X.outwardEdgeCone v₀ v).Nonempty) :
    X.laplace w (preimage w f v₀) = f := by sorry
