-- Prove2me | Theorems.Thm_BruhatTits_unit_smul_eq
-- name    : BruhatTits.unit_smul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:32.542302+00:00
-- url     : https://prove2.me/theorems/da9a36b5-ef49-4242-bab7-023a22e005ab
-- title:
--   Bruhat Tits: unit smul eq
-- statement:
--   The Bruhat Tits construction uses the unit smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L426-L442
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L426-L442

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

theorem BruhatTits.unit_smul_eq (u : Rˣ) (M : BruhatTits.Lattice R) : (Units.map R.subtype u : Kˣ) • M = M := by sorry
