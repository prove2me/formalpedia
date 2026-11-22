-- Prove2me | Theorems.Thm_BruhatTits_eq_dist_iff_monotone
-- name    : BruhatTits.eq_dist_iff_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:41.90618+00:00
-- url     : https://prove2.me/theorems/c0e4ef10-d7c1-4723-b3af-55898601afe2
-- title:
--   Bruhat Tits: eq dist iff monotone
-- statement:
--   Monotone variant of `BruhatTits.eq_dist_iff`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L333-L353
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L333-L353

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

theorem BruhatTits.eq_dist_iff_monotone (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (f : Fin 2 → ℤ),
      Irreducible ϖ ∧ Monotone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 1 - f 0 = n := by sorry
