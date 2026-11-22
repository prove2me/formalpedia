-- Prove2me | Theorems.Thm_BruhatTits_mulBasisScalar_apply
-- name    : BruhatTits.mulBasisScalar_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:08.630291+00:00
-- url     : https://prove2.me/theorems/a9ebc5f4-edf1-4fa9-b55f-6fcabd392075
-- title:
--   Bruhat Tits: mul Basis Scalar apply
-- statement:
--   The Bruhat Tits construction uses the mul Basis Scalar apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L410-L413
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L410-L413

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
open Pointwise
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
omit [DecidableEq ι] [Fintype ι]

theorem BruhatTits.mulBasisScalar_apply (a : Kˣ) (M : BruhatTits.Lattice R) (b : Basis ι R M.M) (i : ι) :
    (mulBasisScalar a b i).val = a.val • (b i).val := by sorry
