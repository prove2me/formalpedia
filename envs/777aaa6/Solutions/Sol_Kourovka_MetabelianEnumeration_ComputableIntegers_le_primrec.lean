-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.le_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:24.581187+00:00
-- url     : https://prove2.me/submissions/d9afef5b-fd6e-4826-9623-0cf5cffb2929

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_toNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_neg_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : PrimrecRel (fun x y : ℤ => x ≤ y) := by
  apply (Primrec.nat_le.comp
    (Primrec.nat_add.comp (toNat_primrec.comp Primrec.fst)
      (toNat_primrec.comp (neg_primrec.comp Primrec.snd)))
    (Primrec.nat_add.comp (toNat_primrec.comp Primrec.snd)
      (toNat_primrec.comp (neg_primrec.comp Primrec.fst)))).of_eq
  intro z
  rcases z with ⟨x, y⟩
  cases x <;> cases y <;> simp [Int.negSucc_eq] <;> omega
end Kourovka.MetabelianEnumeration.ComputableIntegers
