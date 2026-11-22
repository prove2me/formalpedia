-- Prove2me | Theorems.Thm_BruhatTits_mulBasisScalar_toGL
-- name    : BruhatTits.mulBasisScalar_toGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:02.325089+00:00
-- url     : https://prove2.me/theorems/c5fa8d29-f2cf-4f0f-a89e-54fe8a8a7d24
-- title:
--   Bruhat Tits: mul Basis Scalar to GL
-- statement:
--   The Bruhat Tits construction uses the mul Basis Scalar to GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L420-L424
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L420-L424

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

theorem BruhatTits.mulBasisScalar_toGL [IsFractionRing R K] (a : Kˣ) (M : BruhatTits.Lattice R)
    (b : Basis (Fin 2) R M.M) : (mulBasisScalar a b).toGL = GL.diagonal (fun _ ↦ a) * b.toGL := by sorry
