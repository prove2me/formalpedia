-- Prove2me | Theorems.Thm_Basis_smul_twist
-- name    : Basis.smul_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:12:56.532734+00:00
-- url     : https://prove2.me/theorems/c487a0c7-3b88-4c25-b4e8-ee01418ed176
-- title:
--   Basis: smul twist
-- statement:
--   The Basis construction uses the smul twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L491-L505
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L491-L505

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
open Pointwise

theorem Basis.smul_twist (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℤ) :
    ϖ • (b.twist hϖ f).toSubmodule (R := R) = (b.twist hϖ (f + 1)).toSubmodule := by sorry
