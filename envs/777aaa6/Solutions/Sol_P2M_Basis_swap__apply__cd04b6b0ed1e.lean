-- Prove2me | solution 1 for P2M_Basis_swap__apply__cd04b6b0ed1e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:12:12.656565+00:00
-- url     : https://prove2.me/submissions/0828c8e8-9ab5-40c3-8035-c545119f2e50

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
theorem _root_.solution : swap₂ 1 = 0 := rfl
end Basis
