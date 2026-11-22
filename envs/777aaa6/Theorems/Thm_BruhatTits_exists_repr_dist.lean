-- Prove2me | Theorems.Thm_BruhatTits_exists_repr_dist
-- name    : BruhatTits.exists_repr_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:45.104757+00:00
-- url     : https://prove2.me/theorems/dd767671-4720-4fba-9042-baf1cb73b101
-- title:
--   Bruhat Tits: exists repr dist
-- statement:
--   The Bruhat Tits construction uses the exists repr dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L355-L360
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L355-L360

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

theorem BruhatTits.exists_repr_dist (M L : BruhatTits.Lattice R) :
    ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
      Irreducible ϖ ∧ Antitone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 0 - f 1 = dist M L := by sorry
