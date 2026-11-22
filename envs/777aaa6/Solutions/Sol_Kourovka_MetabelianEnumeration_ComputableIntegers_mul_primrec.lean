-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.mul_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:59.607977+00:00
-- url     : https://prove2.me/submissions/61e7919c-bf05-4030-9c67-24ecd6b5d4ea

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_ofNat_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_natAbs_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_neg_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_lt_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution : Primrec₂ (fun x y : ℤ => x * y) := by
  have hprod : Primrec₂ (fun x y : ℤ => ((x.natAbs * y.natAbs : ℕ) : ℤ)) :=
    ofNat_primrec.comp (Primrec.nat_mul.comp
      (natAbs_primrec.comp Primrec.fst) (natAbs_primrec.comp Primrec.snd))
  have hsign : PrimrecPred (fun p : ℤ × ℤ => (p.1 < 0) ↔ (p.2 < 0)) :=
    (Primrec.eq.comp (lt_primrec.comp Primrec.fst (Primrec.const 0)).decide
      (lt_primrec.comp Primrec.snd (Primrec.const 0)).decide).of_eq (fun p => by simp)
  apply (Primrec.ite hsign hprod (neg_primrec.comp hprod)).of_eq
  rintro ⟨x, y⟩
  simp only [Nat.cast_mul, Int.natCast_natAbs]
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · simp [hx, hy, abs_of_neg hx, abs_of_neg hy]
  · simp [hx, hy, abs_of_neg hx, abs_of_nonneg (le_of_not_gt hy)]
  · simp [hx, hy, abs_of_nonneg (le_of_not_gt hx), abs_of_neg hy]
  · simp [hx, hy, abs_of_nonneg (le_of_not_gt hx), abs_of_nonneg (le_of_not_gt hy)]
end Kourovka.MetabelianEnumeration.ComputableIntegers
