-- Prove2me | solution 1 for quotient_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:55:42.520857+00:00
-- url     : https://prove2.me/submissions/5f76f72c-902a-490a-a6fc-a8509d6c3ec9

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra

set_option autoImplicit false
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]
open TensorProduct LinearMap
variable (M)
variable {R M : Type*} [CommRing R] (I : Ideal R) [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [StrongRankCondition (R ⧸ I)]
theorem _root_.solution (b : Basis ι R M) :
    Module.finrank (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) = Fintype.card ι := by
  rw [(TensorProduct.quotientEquivPiOfBasis I b).finrank_eq]
  exact Module.finrank_fintype_fun_eq_card (R ⧸ I)
