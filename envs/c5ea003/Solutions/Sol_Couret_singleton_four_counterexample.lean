-- Prove2me | solution 1 for Couret.singleton_four_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:24.849739+00:00
-- url     : https://prove2.me/submissions/892de2a2-6c90-46cd-95b4-bd391829a3a1

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret



























theorem p2m_local_singleton_four_counterexample :
    2 ∣ total natProduct (.snoc .empty 4) ∧
      ¬ fullSupport natProduct (.snoc .empty 4) 2 := by
  constructor
  · decide
  · rintro ⟨s, hs⟩
    cases s with
    | skip s =>
      cases s
      change 1 = 2 at hs
      omega
    | take s =>
      cases s
      change 1 * 4 = 2 at hs
      omega



end Couret


theorem solution : And
  (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@Couret.total.{0} Nat Couret.natProduct
      (@Couret.Word.snoc.{0} Nat (@Couret.Word.empty.{0} Nat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
  (Not
    (@Couret.fullSupport.{0} Nat Couret.natProduct
      (@Couret.Word.snoc.{0} Nat (@Couret.Word.empty.{0} Nat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := @_root_.Couret.p2m_local_singleton_four_counterexample

