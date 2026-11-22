-- Prove2me | Definitions.Def_BruhatTits_Utils_LinearAlgebra
-- name    : BruhatTits_Utils_LinearAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:41:58.988393+00:00
-- url     : https://prove2.me/theorems/e837ae5c-af15-4f0b-a962-654860cbe8bb
-- title:
--   Linear Algebra
-- statement:
--   Definitions and structural lemmas for Linear Algebra, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
set_option autoImplicit false
section
variable {R M : Type*} [Field R]  [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]
end
section
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]
open TensorProduct LinearMap
variable (M)
noncomputable def quotTensorEquivQuotSMul' (I : Ideal R) :
    (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] M ⧸ (I • ⊤ : Submodule R M) :=
  (quotTensorEquivQuotSMul M I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
variable {R M : Type*} [CommRing R] (I : Ideal R) [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def TensorProduct.quotientEquivPiOfBasis (b : Basis ι R M) :
    (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R ⧸ I] (ι → R ⧸ I) :=
  let f := TensorProduct.piScalarRight R (R ⧸ I) (R ⧸ I) ι
  let g : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] M ⧸ I • ⊤ :=
    (quotTensorEquivQuotSMul M I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let h : M ≃ₗ[R] (ι → R) := b.equivFun
  let h' : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[R] (ι → R) :=
    AlgebraTensorModule.congr (LinearEquiv.refl (R ⧸ I) (R ⧸ I)) h
  g.symm ≪≫ₗ h' ≪≫ₗ f
variable [StrongRankCondition (R ⧸ I)]
end
section
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
instance (p : Submodule R M) : OrderTop { p' : Submodule R M // p ≤ p' } where
  top := ⟨⊤, le_top⟩
  le_top _ _ _ := trivial
instance (p : Submodule R M) : OrderBot { p' : Submodule R M // p ≤ p' } where
  bot := ⟨p, le_rfl⟩
  bot_le p' _ hx := p'.property hx
end
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
end
section
end


