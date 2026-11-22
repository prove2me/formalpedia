-- Prove2me | Theorems.Thm_BruhatTits_inv_self
-- name    : BruhatTits.inv_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:59.919354+00:00
-- url     : https://prove2.me/theorems/7875e7cf-7fc7-4e6c-a80f-8a0d6d816028
-- title:
--   Bruhat Tits: inv self
-- statement:
--   The Bruhat Tits construction uses the inv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L61-L63
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L61-L63

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}

theorem BruhatTits.inv_self (L : Vertices R) : inv L L = 0 := by sorry
