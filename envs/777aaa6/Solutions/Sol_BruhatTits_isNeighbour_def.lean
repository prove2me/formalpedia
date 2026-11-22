-- Prove2me | solution 1 for BruhatTits.isNeighbour_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:09:53.49117+00:00
-- url     : https://prove2.me/submissions/f6db784f-fb34-4d82-9ac8-56258823b10a

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (x y : Vertices R) :
    IsNeighbour x y ↔ inv x y = 1 :=
  Iff.rfl
end BruhatTits
