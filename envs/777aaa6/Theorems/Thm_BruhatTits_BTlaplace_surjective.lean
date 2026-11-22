-- Prove2me | Theorems.Thm_BruhatTits_BTlaplace_surjective
-- name    : BruhatTits.BTlaplace_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:27:22.683221+00:00
-- url     : https://prove2.me/theorems/53f1f36d-11f3-4455-83d3-5bff14cb7cd4
-- title:
--   Bruhat Tits: BTlaplace surjective
-- statement:
--   The Bruhat Tits construction uses the BTlaplace surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Application.lean#L35-L38
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Application.lean#L35-L38

import Definitions.Def_BruhatTits_Graph_Orientation
import Definitions.Def_BruhatTits_Graph_Regular
import Definitions.Def_BruhatTits_Harmonic_Basic
import Definitions.Def_BruhatTits_Harmonic_Application
set_option autoImplicit false
open Classical IsLocalRing
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K]
variable (R : Subring K) [IsDiscreteValuationRing R] [IsFractionRing R K]
variable [Finite (ResidueField R)]
variable (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]

theorem BruhatTits.BTlaplace_surjective : Function.Surjective (BTlaplace R A M) := by sorry
