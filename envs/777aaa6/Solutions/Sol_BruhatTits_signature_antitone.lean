-- Prove2me | solution 1 for BruhatTits.signature_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:47:59.645185+00:00
-- url     : https://prove2.me/submissions/a3567f94-2676-4bd8-87db-c80e21c97b65

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R) :
    Antitone (signature M L) :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose_spec.right.left
end BruhatTits
