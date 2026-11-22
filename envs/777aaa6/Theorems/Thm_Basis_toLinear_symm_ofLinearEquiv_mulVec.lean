-- Prove2me | Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
-- name    : Basis.toLinear_symm_ofLinearEquiv_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:11:40.252982+00:00
-- url     : https://prove2.me/theorems/7086f800-87f9-4f44-ba96-0d757778f295
-- title:
--   Basis: to Linear symm of Linear Equiv mul Vec
-- statement:
--   The Basis construction uses the to Linear symm of Linear Equiv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L593-L605
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L593-L605

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

theorem Basis.toLinear_symm_ofLinearEquiv_mulVec (e : (ι → K) ≃ₗ[K] (ι → K)) (x : ι → K) :
    (Matrix.GeneralLinearGroup.toLin.symm <| .ofLinearEquiv e).val.mulVec x = e x := by sorry
