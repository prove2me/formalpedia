-- Prove2me | Theorems.Thm_Kourovka_exists_diagonal_congruence_iterate
-- name    : Kourovka.exists_diagonal_congruence_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:27.291382+00:00
-- url     : https://prove2.me/theorems/c3e28fd1-158a-44ef-b20a-a5a8dc3d9a29
-- title:
--   Kourovka: exists diagonal congruence iterate
-- statement:
--   One common positive power satisfies independently chosen congruences on both diagonal maps.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DiagonalCongruence.lean#L29-L67
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DiagonalCongruence.lean#L29-L67

import Definitions.Def_Kourovka_CentralLattice
import Definitions.Def_Kourovka_CentralPeriod
import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DiagonalCongruence
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.exists_diagonal_congruence_iterate [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (dA dB : ℤ) (hdA : dA ≠ 0) (hdB : dB ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      (∀ x : Additive (Abelianization A), ∃ y,
        CentralLattice.abelianMap (diagonalLeft (ProductPaths.iterateHom f n)) x - x = dA • y) ∧
      (∀ x : Additive (Abelianization B), ∃ y,
        CentralLattice.abelianMap (diagonalRight (ProductPaths.iterateHom f n)) x - x = dB • y) := by sorry
