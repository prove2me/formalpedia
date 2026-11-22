-- Prove2me | Theorems.Thm_P2M_iUnion__doset_cartanDiag_eq_univ_daed3a7dc61c
-- name    : P2M_iUnion__doset_cartanDiag_eq_univ_daed3a7dc61c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:22:15.319404+00:00
-- url     : https://prove2.me/theorems/fde2ee49-dae6-44df-ad1b-d6b72db8dbf7
-- title:
--   P2 M i Union  doset cartan Diag eq univ daed3a7dc61c: P2 M i Union  doset cartan Diag eq univ daed3a7dc61c
-- statement:
--   `GL₂` is the union of the double cosets `GL₂(R) * D * GL₂(R)` where `D` runs through
--   all diagonal matrices with entries of the form `ϖ ^ n` with descending `n`.
--   This is a disjoint union (see `disjoint_doset_cartanDiag_of_ne`).
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L165-L175
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L165-L175

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}

theorem P2M_iUnion__doset_cartanDiag_eq_univ_daed3a7dc61c : ⋃ (f : Fin k → ℤ) (_ : Antitone f),
    Doset.doset (cartanDiag ϖ hϖ f)
      (Set.range <| GL.map R.subtype)
      (Set.range <| GL.map R.subtype) = Set.univ := by sorry

alias «iUnion₂_doset_cartanDiag_eq_univ» := P2M_iUnion__doset_cartanDiag_eq_univ_daed3a7dc61c
