-- Prove2me | solution 1 for BruhatTits.isChain_of_cons_isChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:10:37.187298+00:00
-- url     : https://prove2.me/submissions/974056d4-b636-4c5b-b430-84a056e8556f

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
theorem _root_.solution {l : List (BruhatTits.Lattice R)} {M : BruhatTits.Lattice R} (hl : l ≠ [])
    (h : (M :: l).IsBruhatTitsChain) : l.IsBruhatTitsChain where
  ne_nil := hl
  isStandardNeighbour := by
    have := h.isStandardNeighbour
    exact List.IsChain.tail this
end BruhatTits
