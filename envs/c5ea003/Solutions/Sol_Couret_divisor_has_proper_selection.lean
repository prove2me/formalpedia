-- Prove2me | solution 1 for Couret.divisor_has_proper_selection
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:56.238686+00:00
-- url     : https://prove2.me/submissions/499d16cb-5eb9-4bbb-b58c-7f7d5b74c9f0

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Theorems.Thm_Couret_Choice_eval_of_not_omitted
import Theorems.Thm_Couret_Choice_eval_of_not_picked
import Theorems.Thm_Couret_divisor_has_selection
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret











theorem p2m_local_divisor_has_proper_selection (w : Word Nat) (hw : w.primeFactors)
    (d : Nat) (hd : d ∣ total natProduct w) (hone : 1 < d)
    (hlt : d < total natProduct w) : properSupport natProduct w d := by
  rcases divisor_has_selection w hw d hd with ⟨s, hs⟩
  have hp : s.picked := by
    by_cases h : s.picked
    · exact h
    · have he := Choice.eval_of_not_picked natProduct s h
      change Choice.eval natProduct s = 1 at he
      omega
  have ho : s.omitted := by
    by_cases h : s.omitted
    · exact h
    · have he := Choice.eval_of_not_omitted natProduct s h
      omega
  exact ⟨s, hp, ho, hs⟩



















end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (d : Nat),
      @Dvd.dvd.{0} Nat Nat.instDvd d (@Couret.total.{0} Nat Couret.natProduct w) →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
          @LT.lt.{0} Nat instLTNat d (@Couret.total.{0} Nat Couret.natProduct w) →
            @Couret.properSupport.{0} Nat Couret.natProduct w d := @_root_.Couret.p2m_local_divisor_has_proper_selection

