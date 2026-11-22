-- Prove2me | Theorems.Thm_Basis_smulGL_twist
-- name    : Basis.smulGL_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:18:44.462182+00:00
-- url     : https://prove2.me/theorems/d60d6d5e-110e-4e7e-aa8a-fe74df29f1ed
-- title:
--   Basis: smul GL twist
-- statement:
--   The Basis construction uses the smul GL twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L447-L450
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L447-L450

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

theorem Basis.smulGL_twist (g : GL ι K) (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℤ) :
    g • b.twist hϖ f = (g • b).twist hϖ f := by sorry
