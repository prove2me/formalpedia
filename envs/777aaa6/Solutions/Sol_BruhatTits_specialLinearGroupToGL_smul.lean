-- Prove2me | solution 1 for BruhatTits.specialLinearGroupToGL_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:24:05.055562+00:00
-- url     : https://prove2.me/submissions/b1618ccf-a9ff-4d8e-96f8-6869b67ef6b4

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation

set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
namespace BruhatTits
theorem _root_.solution (g : Matrix.SpecialLinearGroup (Fin 2) K) (L : BruhatTits.Lattice R) :
    g.toGL • L = g • L := rfl
end BruhatTits
