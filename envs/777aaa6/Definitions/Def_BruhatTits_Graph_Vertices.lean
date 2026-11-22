-- Prove2me | Definitions.Def_BruhatTits_Graph_Vertices
-- name    : BruhatTits_Graph_Vertices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:07:48.945689+00:00
-- url     : https://prove2.me/theorems/779b6bf5-2e3b-4d9b-b466-0d51e761e9cc
-- title:
--   Vertices
-- statement:
--   Definitions and structural lemmas for Vertices, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_BruhatTits_dist_inv_isSimilar

set_option autoImplicit false
namespace BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
def Vertices : Type _ :=
  Quotient (Lattice.IsSimilar.setoid R)
variable {R}
abbrev Vertices.mk (L : BruhatTits.Lattice R) : Vertices R := ⟦L⟧
noncomputable def inv (L M : Vertices R) : ℕ :=
 Quotient.lift₂ dist dist_inv_isSimilar L M
open Pointwise
end BruhatTits


