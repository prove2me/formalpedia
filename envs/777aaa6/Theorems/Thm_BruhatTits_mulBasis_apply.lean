-- Prove2me | Theorems.Thm_BruhatTits_mulBasis_apply
-- name    : BruhatTits.mulBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:52.506169+00:00
-- url     : https://prove2.me/theorems/5cb62f63-d7d6-4919-b71a-33b9f44530a0
-- title:
--   Bruhat Tits: mul Basis apply
-- statement:
--   The Bruhat Tits construction uses the mul Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L415-L418
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L415-L418

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

theorem BruhatTits.mulBasis_apply (g : GL ι K) {M : Submodule R (ι → K)} (b : Basis ι R M) (i : ι) :
    (mulBasis g b i).val = g *ᵥ (b i).val := by sorry
