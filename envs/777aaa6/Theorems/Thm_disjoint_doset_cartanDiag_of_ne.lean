-- Prove2me | Theorems.Thm_disjoint_doset_cartanDiag_of_ne
-- name    : disjoint_doset_cartanDiag_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:21:30.255189+00:00
-- url     : https://prove2.me/theorems/d216dedd-ff8b-4c13-b6d1-b0594dbc1cd2
-- title:
--   disjoint doset cartan Diag of ne: disjoint doset cartan Diag of ne
-- statement:
--   The double cosets `GL₂(R) * D * GL₂(R)`, where `D` runs through
--   all diagonal matrices with entries of the form `ϖ ^ n` with descending `n`, are pairwise
--   disjoint.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L181-L194
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L181-L194

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
open scoped Function

theorem disjoint_doset_cartanDiag_of_ne :
    Pairwise (Disjoint on fun f : { f : Fin k → ℤ | Antitone f } ↦
      Doset.doset (cartanDiag ϖ hϖ f.1) (Set.range <| GL.map R.subtype)
        (Set.range <| GL.map R.subtype)) := by sorry
