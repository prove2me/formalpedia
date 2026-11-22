-- Prove2me | solution 1 for BruhatTits.isStandard_of_list_isStandard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:23:59.368576+00:00
-- url     : https://prove2.me/submissions/d5cd5d4a-438a-4fb2-8d13-8c733b22ca49

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution {x y : Vertices R} {p : BTgraph.Walk x y}
    (l : List (BruhatTits.Lattice R)) (hleq : l.map (fun L ↦ ⟦L⟧) = p.support) (hl : l.IsStandard) :
    p.IsStandard := by
  use l
end BruhatTits
