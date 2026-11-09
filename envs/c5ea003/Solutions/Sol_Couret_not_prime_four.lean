-- Prove2me | solution 1 for Couret.not_prime_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:13.994712+00:00
-- url     : https://prove2.me/submissions/f9a68fc1-2f58-47df-a7a6-866a147bc763

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





























theorem p2m_local_not_prime_four : ¬ PrimeNat 4 := by
  intro h
  have hd := h.2 2 (by decide : 2 ∣ 4)
  omega

end Couret


theorem solution : Not (Couret.PrimeNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := @_root_.Couret.p2m_local_not_prime_four

