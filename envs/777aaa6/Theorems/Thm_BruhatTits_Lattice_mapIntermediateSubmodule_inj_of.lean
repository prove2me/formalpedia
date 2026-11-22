-- Prove2me | Theorems.Thm_BruhatTits_Lattice_mapIntermediateSubmodule_inj_of
-- name    : BruhatTits.Lattice.mapIntermediateSubmodule_inj_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:57:59.90104+00:00
-- url     : https://prove2.me/theorems/85ba2bf9-9214-43eb-b872-05bf0382751d
-- title:
--   Lattice: map Intermediate Submodule inj of
-- statement:
--   `Lattice.mapIntermediateSubmodule` is injective on submodules between `ϖ L` and `L``.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L235-L261
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L235-L261

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
open BruhatTits
set_option synthInstance.maxHeartbeats 30000
open IsLocalRing
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000

theorem BruhatTits.Lattice.mapIntermediateSubmodule_inj_of (L : BruhatTits.Lattice R) (M₁ M₂ : Submodule R (Fin 2 → K))
    (hle₁ : M₁ ≤ L.M) (hge₁ : IsLocalRing.maximalIdeal R • L.M ≤ M₁)
    (hle₂ : M₂ ≤ L.M) (hge₂ : IsLocalRing.maximalIdeal R • L.M ≤ M₂)
    (h : L.mapIntermediateSubmodule M₁ = L.mapIntermediateSubmodule M₂) :
    M₁ = M₂ := by sorry
