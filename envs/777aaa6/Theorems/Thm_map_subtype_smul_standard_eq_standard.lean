-- Prove2me | Theorems.Thm_map_subtype_smul_standard_eq_standard
-- name    : map_subtype_smul_standard_eq_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:16.509271+00:00
-- url     : https://prove2.me/theorems/61a90ee5-05d8-422a-8750-f5c8dd85063f
-- title:
--   map subtype smul standard eq standard: map subtype smul standard eq standard
-- statement:
--   The map subtype smul standard eq standard construction uses the map subtype smul standard eq standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L725-L754
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L725-L754

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits

theorem map_subtype_smul_standard_eq_standard (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map R.subtype g • Lattice.standard R = Lattice.standard R := by sorry
