-- Prove2me | solution 1 for Basis.smulGL_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:17:57.344501+00:00
-- url     : https://prove2.me/submissions/046930fe-f198-409a-a5d5-0e10fff654e1

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
variable [DecidableEq ι] [Fintype ι]
namespace Basis
theorem _root_.solution (g : GL ι K) (b : Basis ι K (ι → K)) :
    g • b = b.map (g.toLin.toLinearEquiv) :=
  rfl
end Basis
