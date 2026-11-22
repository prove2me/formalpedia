-- Prove2me | Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
-- name    : P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:43:05.466883+00:00
-- url     : https://prove2.me/theorems/80d30c7f-5bbd-4d03-9d7f-eabe4986f95f
-- title:
--   P2 M Linear Map to Matrix  mul Vec bruhat2024 4481c521c4b9: P2 M Linear Map to Matrix  mul Vec bruhat2024 4481c521c4b9
-- statement:
--   The P2 M Linear Map to Matrix  mul Vec bruhat2024 4481c521c4b9 construction uses the P2 M Linear Map to Matrix  mul Vec bruhat2024 4481c521c4b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L248-L263
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L248-L263

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false

theorem P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9 {R : Type*} [CommSemiring R]
    {n : Type*} [DecidableEq n] [Fintype n] (f : (n → R) →ₗ[R] (n → R)) (x : n → R) :
    f.toMatrix'.mulVec x = f x := by sorry

alias «LinearMap».«toMatrix'_mulVec_bruhat2024» := P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
