-- Prove2me | Definitions.Def_Kourovka_DiagonalCongruence
-- name    : Kourovka_DiagonalCongruence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:33:50.317998+00:00
-- url     : https://prove2.me/theorems/59c557f4-cf30-4292-b6cf-ff5b60ada02a
-- title:
--   Diagonal Congruence
-- statement:
--   Definitions and structural lemmas for Diagonal Congruence, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DiagonalCongruence.lean

import Definitions.Def_Kourovka_CentralLattice
import Definitions.Def_Kourovka_CentralPeriod
import Definitions.Def_Kourovka_PathExpansion
set_option autoImplicit true
namespace Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
def diagonalLeft (f : A × B →* A × B) : A →* A :=
  (MonoidHom.fst A B).comp (ProductHom.left f)
def diagonalRight (f : A × B →* A × B) : B →* B :=
  (MonoidHom.snd A B).comp (ProductHom.right f)
end Kourovka


