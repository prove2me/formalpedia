-- Prove2me | Theorems.Thm_SimpleGraph_laplaceHom_surjective
-- name    : SimpleGraph.laplaceHom_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:00:17.611438+00:00
-- url     : https://prove2.me/theorems/134aff28-eb84-45ee-a9a0-bd3bd50bf264
-- title:
--   Simple Graph: laplace Hom surjective
-- statement:
--   The Simple Graph construction uses the laplace Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L768-L770
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L768-L770

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
variable {X : SimpleGraph V}
variable [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ)

theorem SimpleGraph.laplaceHom_surjective (htree : X.IsTree) (hdeg : ∀ (v : V), 2 ≤ X.degree v) :
    Function.Surjective (X.laplaceHom (M := M) w) := by sorry
