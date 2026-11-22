-- Prove2me | Theorems.Thm_BruhatTits_eq_dist_iff
-- name    : BruhatTits.eq_dist_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:17.920343+00:00
-- url     : https://prove2.me/theorems/14c8ea74-dd8b-40db-80a5-3418607f8c90
-- title:
--   Bruhat Tits: eq dist iff
-- statement:
--   A rephrasing of uniqueness of signatures in terms of the distance of lattices.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L281-L304
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L281-L304

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

theorem BruhatTits.eq_dist_iff (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (f : Fin 2 → ℤ),
      Irreducible ϖ ∧
        Antitone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 0 - f 1 = n := by sorry
