-- Prove2me | solution 1 for BruhatTits.signatureBasisTarget_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:48:00.078725+00:00
-- url     : https://prove2.me/submissions/e5901c87-0ecb-4843-b06b-e9a63c6c2ecd

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
theorem _root_.solution (M L : BruhatTits.Lattice R) (i : Fin 2) :
    signatureBasisTarget M L i =
      (signatureϖ M L ^ signature M L i : K) • (signatureBasisSource M L i).val :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose_spec.right.right i
end BruhatTits
