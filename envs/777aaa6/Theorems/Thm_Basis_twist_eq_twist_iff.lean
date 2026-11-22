-- Prove2me | Theorems.Thm_Basis_twist_eq_twist_iff
-- name    : Basis.twist_eq_twist_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:14:55.020699+00:00
-- url     : https://prove2.me/theorems/d4737522-a81e-4306-8fcc-3742986e301e
-- title:
--   Basis: twist eq twist iff
-- statement:
--   The Basis construction uses the twist eq twist iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L229-L237
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L229-L237

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
open BigOperators

theorem Basis.twist_eq_twist_iff [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f g : ι → ℤ) :
    (b.twist hϖ f).toSubmodule (R := R) = (b.twist hϖ g).toSubmodule (R := R) ↔ g = f := by sorry
