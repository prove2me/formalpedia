-- Prove2me | Definitions.Def_mme_more_asymmetry_raw_source_compatibility
-- name    : mme_more_asymmetry_raw_source_compatibility
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-12T17:04:43.620461+00:00
-- url     : https://prove2.me/theorems/67db32f3-c1f8-4d2d-9299-bac372e980eb
-- title:
--   More Asymmetry raw-source compatibility interface
-- statement:
--   For a finite More Asymmetry data bundle $D$ and its concrete recursive stages $A$, this interface records the source-level information needed before the raw tensor assembly. A common order-three tensor is supplied as the factor source; each literal stage source restricts to that factor source, and the finite Kronecker product of those factor sources is isomorphic to the declared six-symmetrised $CW_5^{\otimes 4}$ source power. The interface does not assert the final restriction, the intact-template matrix multiplication assembly, or any rate inequality. It isolates precisely the source and exponent compatibility that the raw assembly theorem must consume.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.1 and 6.1--6.6; source compatibility between the literal fourth-power constituents, the six-region symmetrisation, and the physical tensor power.

import Definitions.Def_mme_recursive_yz_stage_certificate
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_tensor_quotient

open MME MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

namespace MME.RecursiveYZ.Certificate

/--
The finite source-level data needed by the raw half of the More Asymmetry
assembly. Each concrete recursive stage source restricts to one common
factor source, and the resulting finite Kronecker product is isomorphic to
the six-symmetrised fourth-power CW source at the declared physical power.

This interface deliberately contains no tensor restriction to the final
campaign source and no template/MM conclusion. Those are consequences of
the separate raw and intact-template assembly theorems.
-/
structure MoreAsymmetryRawSourceCompatibility
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (K : Type u) [Field K] where
  source : TensorObj K 3
  factor_restrict :
    ∀ j, TensorObj.Restrict ((A j).raw K) source
  ambient_isomorphic :
    TensorObj.Isomorphic
      (TensorObj.kronFin D.factors (fun _ : Fin D.factors => source))
      ((sixSymmetrization (StothersFourth.cwFourthObj K 5)).kronPow D.power)

end MME.RecursiveYZ.Certificate


