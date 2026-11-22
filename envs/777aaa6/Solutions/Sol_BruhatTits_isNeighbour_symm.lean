-- Prove2me | solution 1 for BruhatTits.isNeighbour_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:12:54.887051+00:00
-- url     : https://prove2.me/submissions/9c35aab5-309f-46dc-8605-755f345cd378

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_BruhatTits_isNeighbour_def
import Theorems.Thm_BruhatTits_inv_symm


set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (x y : Vertices R) :
    IsNeighbour x y ↔ IsNeighbour y x := by
  classical
  rw [isNeighbour_def, isNeighbour_def, inv_symm]
end BruhatTits
