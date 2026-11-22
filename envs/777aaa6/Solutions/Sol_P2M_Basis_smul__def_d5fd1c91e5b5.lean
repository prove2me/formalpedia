-- Prove2me | solution 1 for P2M_Basis_smul__def_d5fd1c91e5b5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:20:58.879+00:00
-- url     : https://prove2.me/submissions/bdbef383-5bc4-4182-8fab-dd67c2c0cdfb

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
variable [Fintype ι]
namespace Basis
theorem _root_.solution (a : Kˣ) (b : Basis ι K (ι → K)) : a • b = b.twist' (fun _ ↦ a) := rfl
end Basis
