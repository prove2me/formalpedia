-- Prove2me | solution 1 for P2M_Basis_swap__symm_e7ab2aa72738
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:11:40.619508+00:00
-- url     : https://prove2.me/submissions/c2820dbd-c694-40f1-98fe-a7c451765c2b

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
theorem _root_.solution : swap₂.symm = swap₂ := rfl
end Basis
