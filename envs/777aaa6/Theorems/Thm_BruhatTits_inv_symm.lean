-- Prove2me | Theorems.Thm_BruhatTits_inv_symm
-- name    : BruhatTits.inv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:54.703172+00:00
-- url     : https://prove2.me/theorems/0ceff08f-8284-4153-92c9-de7f65340ad0
-- title:
--   Bruhat Tits: inv symm
-- statement:
--   The Bruhat Tits construction uses the inv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L56-L59
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L56-L59

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}

theorem BruhatTits.inv_symm (L M : Vertices R) : inv L M = inv M L := by sorry
