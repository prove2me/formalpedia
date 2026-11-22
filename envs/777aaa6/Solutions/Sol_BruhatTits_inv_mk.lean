-- Prove2me | solution 1 for BruhatTits.inv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:09:56.113689+00:00
-- url     : https://prove2.me/submissions/0d0872a5-fb23-44e0-a937-4bfa0d913cac

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
namespace BruhatTits
theorem _root_.solution (L M : BruhatTits.Lattice R) :
    inv (Quotient.mk'' L) (Quotient.mk'' M) = dist L M :=
  rfl
end BruhatTits
