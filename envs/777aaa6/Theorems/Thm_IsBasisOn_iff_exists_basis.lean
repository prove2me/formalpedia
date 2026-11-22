-- Prove2me | Theorems.Thm_IsBasisOn_iff_exists_basis
-- name    : IsBasisOn.iff_exists_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:00:34.156617+00:00
-- url     : https://prove2.me/theorems/9aed03b3-af92-402b-a8a7-66c947c5b762
-- title:
--   Is Basis On: iff exists basis
-- statement:
--   A family of elements of `V` is a basis on `M` in the sense of `IsBasisOn` if and only if
--   there exists a basis of `M` that agrees with `b`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/IsBasisOn.lean#L103-L109
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/IsBasisOn.lean#L103-L109

import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_BruhatTits_Utils_IsBasisOn
set_option autoImplicit false
variable {R K V ι : Type*} [CommSemiring R] [Semiring K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
open IsBasisOn

theorem IsBasisOn.iff_exists_basis (b : ι → V) (M : Submodule R V) :
    IsBasisOn b M ↔ ∃ (bM : Basis ι R M), ∀ i, bM i = b i := by sorry
