-- Prove2me | Theorems.Thm_P2M_BruhatTits_eq_dist_iff__2efec8b3b981
-- name    : P2M_BruhatTits_eq_dist_iff__2efec8b3b981
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:25.934113+00:00
-- url     : https://prove2.me/theorems/cfed27a0-d5f5-423d-858d-e4434cea0054
-- title:
--   P2 M Bruhat Tits eq dist iff  2efec8b3b981: P2 M Bruhat Tits eq dist iff  2efec8b3b981
-- statement:
--   Variant of `BruhatTits.eq_dist_iff` where the signature is unwrapped as two integers `a` and
--   `b`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L308-L330
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L308-L330

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

theorem P2M_BruhatTits_eq_dist_iff__2efec8b3b981 (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (a b : ℤ), Irreducible ϖ ∧
         b ≤ a ∧ bL 0 = ϖ.val ^ a • (bM 0).val ∧ bL 1 = ϖ.val ^ b • (bM 1).val ∧ a - b = n := by sorry

alias «BruhatTits».«eq_dist_iff₂» := P2M_BruhatTits_eq_dist_iff__2efec8b3b981
