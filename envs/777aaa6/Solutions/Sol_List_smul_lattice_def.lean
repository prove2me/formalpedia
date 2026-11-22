-- Prove2me | solution 1 for List.smul_lattice_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:11:31.620517+00:00
-- url     : https://prove2.me/submissions/3ef1525e-affc-47e3-828d-07e7d8546097

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
open IsLocalRing
namespace BruhatTits
namespace _root_.List
theorem _root_.solution (g : GL (Fin 2) K) (l : List (BruhatTits.Lattice R)) :
    g • l = l.map (fun L ↦ g • L) :=
  rfl
end _root_.List
end BruhatTits
