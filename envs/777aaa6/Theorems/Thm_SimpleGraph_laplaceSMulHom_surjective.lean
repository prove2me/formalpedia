-- Prove2me | Theorems.Thm_SimpleGraph_laplaceSMulHom_surjective
-- name    : SimpleGraph.laplaceSMulHom_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:00:20.489362+00:00
-- url     : https://prove2.me/theorems/54174007-44aa-4791-9850-21b2f6fdc7cb
-- title:
--   Simple Graph: laplace SMul Hom surjective
-- statement:
--   The Simple Graph construction uses the laplace SMul Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L845-L847
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean#L845-L847

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
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {V : Type*} [DecidableEq V]
variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]
attribute [instance] arrowAction
variable {G} {X}
variable [∀ v, Fintype (X.neighborSet v)] (w : V →[G] Rˣ)

theorem SimpleGraph.laplaceSMulHom_surjective (htree : X.IsTree) (hdeg : ∀ (v : V), 2 ≤ X.degree v) :
    Function.Surjective (laplaceSMulHom (M := M) (X := X) w) := by sorry
