-- Prove2me | Definitions.Def_BruhatTits_Harmonic_Application
-- name    : BruhatTits_Harmonic_Application
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:26:28.879831+00:00
-- url     : https://prove2.me/theorems/46cdc9ab-660e-4b18-b987-755cc17bd3a3
-- title:
--   Application
-- statement:
--   Definitions and structural lemmas for Application, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Application.lean

import Definitions.Def_BruhatTits_Graph_Orientation
import Definitions.Def_BruhatTits_Graph_Regular
import Definitions.Def_BruhatTits_Harmonic_Basic
set_option autoImplicit false
open Classical IsLocalRing
suppress_compilation
namespace BruhatTits
variable {K : Type*} [Field K]
variable (R : Subring K) [IsDiscreteValuationRing R] [IsFractionRing R K]
variable [Finite (ResidueField R)]
def BTlaplace (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] :
    ((BTgraph (R := R)).edgeSet → M) →ₗ[A] (Vertices R → M) :=
  (BTgraph (R := R)).laplaceLinearMap (BTweight A)
variable (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]


