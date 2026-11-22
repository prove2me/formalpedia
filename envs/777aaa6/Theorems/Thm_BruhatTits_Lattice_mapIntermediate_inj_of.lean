-- Prove2me | Theorems.Thm_BruhatTits_Lattice_mapIntermediate_inj_of
-- name    : BruhatTits.Lattice.mapIntermediate_inj_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:10.171174+00:00
-- url     : https://prove2.me/theorems/47f86538-faf6-4ed6-9dff-ce0d95786e3c
-- title:
--   Lattice: map Intermediate inj of
-- statement:
--   `Lattice.mapIntermediate` is injective on lattices between `ϖ L` and `L``.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L264-L270
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L264-L270

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

theorem BruhatTits.Lattice.mapIntermediate_inj_of (L M₁ M₂ : BruhatTits.Lattice R)
    (hle₁ : M₁.M ≤ L.M) (hge₁ : IsLocalRing.maximalIdeal R • L.M ≤ M₁.M)
    (hle₂ : M₂.M ≤ L.M) (hge₂ : IsLocalRing.maximalIdeal R • L.M ≤ M₂.M)
    (h : L.mapIntermediate M₁ = L.mapIntermediate M₂) :
    M₁ = M₂ := by sorry
