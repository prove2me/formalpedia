-- Prove2me | Theorems.Thm_Basis_twist_le_twist_iff
-- name    : Basis.twist_le_twist_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:12:57.791347+00:00
-- url     : https://prove2.me/theorems/da94bb4c-dfdc-4c1c-851a-2c8892c07413
-- title:
--   Basis: twist le twist iff
-- statement:
--   The Basis construction uses the twist le twist iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L168-L227
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean#L168-L227

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

theorem Basis.twist_le_twist_iff [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f g : ι → ℤ) :
    (b.twist hϖ f).toSubmodule (R := R) ≤ (b.twist hϖ g).toSubmodule (R := R) ↔ g ≤ f := by sorry
