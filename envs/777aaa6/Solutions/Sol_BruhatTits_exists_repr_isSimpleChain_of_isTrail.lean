-- Prove2me | solution 1 for BruhatTits.exists_repr_isSimpleChain_of_isTrail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:29:02.677152+00:00
-- url     : https://prove2.me/submissions/8b5bd0d2-c32e-4c54-89bd-3460b1f4bb7f

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
import Theorems.Thm_SimpleGraph_Walk_exists_repr_isChain
import Theorems.Thm_BruhatTits_isSimpleChain_of_isTrail_aux

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution {x y : Vertices R} (p : BTgraph.Walk x y)
    (hp : p.IsTrail) :
    ∃ (l : List (BruhatTits.Lattice R)), l.IsSimpleChain ∧ l.map (fun L ↦ ⟦L⟧) = p.support := by
  obtain ⟨l, hl, heq⟩ := p.exists_repr_isChain
  refine ⟨l, ⟨hl, ?_⟩, heq⟩
  apply isSimpleChain_of_isTrail_aux p hp _ heq
end BruhatTits
