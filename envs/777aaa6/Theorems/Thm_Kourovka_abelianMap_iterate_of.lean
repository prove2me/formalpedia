-- Prove2me | Theorems.Thm_Kourovka_abelianMap_iterate_of
-- name    : Kourovka.abelianMap_iterate_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:23.047923+00:00
-- url     : https://prove2.me/theorems/bbecba31-b1c8-4c3f-bdab-9cd6332f8fa5
-- title:
--   Kourovka: abelian Map iterate of
-- statement:
--   The Kourovka construction uses the abelian Map iterate of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DiagonalCongruence.lean#L19-L26
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DiagonalCongruence.lean#L19-L26

import Definitions.Def_Kourovka_CentralLattice
import Definitions.Def_Kourovka_CentralPeriod
import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DiagonalCongruence
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.abelianMap_iterate_of (f : G →* G) (n : ℕ) (x : G) :
    (CentralLattice.abelianMap f)^[n] (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (f^[n] x)) := by sorry
