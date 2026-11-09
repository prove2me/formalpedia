-- Prove2me | solution 1 for Couret.properSupport_iff_nontrivial_divisor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:14.209383+00:00
-- url     : https://prove2.me/submissions/614a2ac3-325b-4216-a10c-1ba783de00fe

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Theorems.Thm_Couret_divisor_has_proper_selection
import Theorems.Thm_Couret_properSupport_is_nontrivial_divisor
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret





theorem primeFactors_atLeastTwo (w : Word Nat) (h : w.primeFactors) :
    w.atLeastTwo := by
  induction w with
  | empty => exact True.intro
  | snoc w p ih => exact ⟨ih h.1, h.2.1⟩







theorem p2m_local_properSupport_iff_nontrivial_divisor (w : Word Nat) (hw : w.primeFactors)
    (d : Nat) :
    properSupport natProduct w d ↔
      d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w := by
  constructor
  · exact properSupport_is_nontrivial_divisor w (primeFactors_atLeastTwo w hw) d
  · rintro ⟨hd, hone, hlt⟩
    exact divisor_has_proper_selection w hw d hd hone hlt

















end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (d : Nat),
      Iff (@Couret.properSupport.{0} Nat Couret.natProduct w d)
        (And (@Dvd.dvd.{0} Nat Nat.instDvd d (@Couret.total.{0} Nat Couret.natProduct w))
          (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
            (@LT.lt.{0} Nat instLTNat d (@Couret.total.{0} Nat Couret.natProduct w)))) := @_root_.Couret.p2m_local_properSupport_iff_nontrivial_divisor

