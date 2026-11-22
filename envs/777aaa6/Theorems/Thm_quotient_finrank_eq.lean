-- Prove2me | Theorems.Thm_quotient_finrank_eq
-- name    : quotient_finrank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:47:42.99672+00:00
-- url     : https://prove2.me/theorems/2fb96c51-9286-4712-979c-c5d115f59aa1
-- title:
--   quotient finrank eq: quotient finrank eq
-- statement:
--   If `M` is free, the rank of `M ⧸ IM`as an `R ⧸ I`-module is the rank of `M` as an `R`-module.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L149-L152
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L149-L152

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

theorem quotient_finrank_eq (b : Basis ι R M) :
    Module.finrank (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) = Fintype.card ι := by sorry
