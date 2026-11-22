-- Prove2me | solution 1 for P2M_Basis_swap__apply__280e1e1cec15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:12:01.924756+00:00
-- url     : https://prove2.me/submissions/ad37e819-e52e-4b9d-a77b-98b38e8c1e66

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
namespace Basis
theorem _root_.solution : swap₂ 0 = 1 := rfl
end Basis
