-- Prove2me | Theorems.Thm_Lattice_standard_M
-- name    : Lattice.standard_M
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:15:03.033568+00:00
-- url     : https://prove2.me/theorems/c5e11a3b-6983-4daa-a41e-9ab6a4ac2726
-- title:
--   Lattice: standard M
-- statement:
--   The Lattice construction uses the standard M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L711-L722
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L711-L722

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits

theorem Lattice.standard_M :
    (Lattice.standard R).M = LinearMap.range ((Algebra.linearMap R K).compLeft _) := by sorry
