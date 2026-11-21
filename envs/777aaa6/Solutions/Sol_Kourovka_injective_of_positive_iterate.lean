-- Prove2me | solution 1 for Kourovka.injective_of_positive_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:02.801484+00:00
-- url     : https://prove2.me/submissions/905ecb58-6396-4d2f-a052-8a2f08b6d1db

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian

set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka
theorem _root_.solution {X : Type*} (f : X → X) {n : ℕ}
    (hn : 0 < n) (hi : Function.Injective f^[n]) : Function.Injective f := by
  intro x y hxy
  apply hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hxy]
end Kourovka
