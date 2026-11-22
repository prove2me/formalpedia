-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.nat_pow_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:45:33.516618+00:00
-- url     : https://prove2.me/submissions/a1ebf907-3876-4ee2-b458-a6fca4c583c1

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec₂ (fun a n : ℕ => a ^ n) := by
  have h := Primrec.nat_rec (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  apply h.of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ih]
end Kourovka.MetabelianEnumeration.ComputableIntegers
