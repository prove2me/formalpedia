-- Prove2me | solution 1 for Couret.fullSupport_iff_divisor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:31.488199+00:00
-- url     : https://prove2.me/submissions/2206a8fd-c87a-4509-b86c-60e7b27c9695

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Theorems.Thm_Couret_divisor_has_selection
import Theorems.Thm_Couret_selectedProduct_dvd_total
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret









theorem p2m_local_fullSupport_iff_divisor (w : Word Nat) (hw : w.primeFactors) (d : Nat) :
    fullSupport natProduct w d ↔ d ∣ total natProduct w := by
  constructor
  · rintro ⟨s, rfl⟩
    exact selectedProduct_dvd_total s
  · exact divisor_has_selection w hw d





















end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (d : Nat),
      Iff (@Couret.fullSupport.{0} Nat Couret.natProduct w d)
        (@Dvd.dvd.{0} Nat Nat.instDvd d (@Couret.total.{0} Nat Couret.natProduct w)) := @_root_.Couret.p2m_local_fullSupport_iff_divisor

