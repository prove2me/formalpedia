-- Prove2me | solution 1 for Kourovka.abelianMap_iterate_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:43.143097+00:00
-- url     : https://prove2.me/submissions/002bed3a-e1b8-4a27-bf5e-948e0a501b0e

import Definitions.Def_Kourovka_CentralLattice
import Definitions.Def_Kourovka_CentralPeriod
import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DiagonalCongruence

set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (f : G →* G) (n : ℕ) (x : G) :
    (CentralLattice.abelianMap f)^[n] (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (f^[n] x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl
end Kourovka
