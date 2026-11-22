-- Prove2me | Theorems.Thm_BruhatTits_inv_mk
-- name    : BruhatTits.inv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:45.086285+00:00
-- url     : https://prove2.me/theorems/eb8d4860-3622-4903-bbd1-5a2851a1488c
-- title:
--   Bruhat Tits: inv mk
-- statement:
--   The Bruhat Tits construction uses the inv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L52-L54
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L52-L54

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}

theorem BruhatTits.inv_mk (L M : BruhatTits.Lattice R) :
    inv (Quotient.mk'' L) (Quotient.mk'' M) = dist L M := by sorry

attribute [defeq] BruhatTits.inv_mk
