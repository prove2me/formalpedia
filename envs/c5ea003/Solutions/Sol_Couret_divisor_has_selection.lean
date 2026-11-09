-- Prove2me | solution 1 for Couret.divisor_has_selection
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:45:23.936968+00:00
-- url     : https://prove2.me/submissions/4afc2fa0-1d8f-493d-8375-3fe82713ae80

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







theorem p2m_local_divisor_has_selection (w : Word Nat) (hw : w.primeFactors)
    (d : Nat) (hd : d ∣ total natProduct w) :
    ∃ s : Choice w, Choice.eval natProduct s = d := by
  induction w generalizing d with
  | empty =>
    have hdone : d = 1 := Nat.eq_one_of_dvd_one hd
    exact ⟨.empty, hdone.symm⟩
  | snoc w p ih =>
    change d ∣ total natProduct w * p at hd
    rcases Nat.dvd_mul.mp hd with ⟨d₁, d₂, h₁, h₂, he⟩
    rcases ih hw.1 d₁ h₁ with ⟨s, hs⟩
    rcases hw.2.2 d₂ h₂ with hskip | htake
    · refine ⟨.skip s p, hs.trans ?_⟩
      simpa only [hskip, Nat.mul_one] using he
    · refine ⟨.take s p, ?_⟩
      change Choice.eval natProduct s * p = d
      rw [hs]
      simpa only [htake] using he























end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (d : Nat),
      @Dvd.dvd.{0} Nat Nat.instDvd d (@Couret.total.{0} Nat Couret.natProduct w) →
        @Exists.{1} (@Couret.Choice.{0} Nat w) fun s =>
          @Eq.{1} Nat (@Couret.Choice.eval.{0} Nat Couret.natProduct w s) d := @_root_.Couret.p2m_local_divisor_has_selection

