-- Prove2me | Theorems.Thm_Basis_smul_pow_twist
-- name    : Basis.smul_pow_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:18:36.820264+00:00
-- url     : https://prove2.me/theorems/2e2690af-9fc9-42ac-b881-40f33e7ddfb0
-- title:
--   Basis: smul pow twist
-- statement:
--   The Basis construction uses the smul pow twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L517-L535
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L517-L535

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

theorem Basis.smul_pow_twist (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℤ) (k : ℤ) :
    ϖ.val ^ k • (b.twist hϖ f).toSubmodule (R := R) = (b.twist hϖ (f + k)).toSubmodule := by sorry
