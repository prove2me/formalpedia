-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.add_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:26.177855+00:00
-- url     : https://prove2.me/submissions/7db62c33-6681-44f6-9312-8363977a5dc2

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_toNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_subNat_eq
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_subNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_neg_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec₂ (fun x y : ℤ => x + y) := by
  have hp : Primrec₂ (fun x y : ℤ => x.toNat + y.toNat) :=
    Primrec.nat_add.comp (toNat_primrec.comp Primrec.fst) (toNat_primrec.comp Primrec.snd)
  have hn : Primrec₂ (fun x y : ℤ => (-x).toNat + (-y).toNat) :=
    Primrec.nat_add.comp (toNat_primrec.comp (neg_primrec.comp Primrec.fst))
      (toNat_primrec.comp (neg_primrec.comp Primrec.snd))
  apply (subNat_primrec.comp hp hn).of_eq
  intro z
  rw [subNat_eq]
  rcases z with ⟨x, y⟩
  cases x <;> cases y <;> simp [Int.negSucc_eq] <;> omega
end Kourovka.MetabelianEnumeration.ComputableIntegers
