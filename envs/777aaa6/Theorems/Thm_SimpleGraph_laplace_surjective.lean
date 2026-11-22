-- Prove2me | Theorems.Thm_SimpleGraph_laplace_surjective
-- name    : SimpleGraph.laplace_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:58.560178+00:00
-- url     : https://prove2.me/theorems/b71aa992-2c60-4d83-929b-5098b93fb90b
-- title:
--   Simple Graph: laplace surjective
-- statement:
--   If `X` is a tree, the Laplacian on `X` is surjective.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L732-L740
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L732-L740

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

theorem SimpleGraph.laplace_surjective {X : SimpleGraph V} (htree : IsTree X) [∀ v, Fintype (X.neighborSet v)]
    (w : V → Aˣ) (hmindeg : ∀ v, 2 ≤ X.degree v) : Function.Surjective (X.laplace (M := M) w) := by sorry
