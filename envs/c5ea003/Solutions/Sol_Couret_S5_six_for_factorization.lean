-- Prove2me | solution 1 for Couret.S5.six_for_factorization
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:01.808694+00:00
-- url     : https://prove2.me/submissions/1544acb6-591e-474e-b1f8-fda6488550ba

import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
import Std
import Theorems.Thm_Couret_S5_full_equals_proper_of_six
import Theorems.Thm_Couret_fullSupport_mod30_iff_divisor
import Theorems.Thm_Couret_properSupport_mod30_iff_divisor
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
namespace Couret
namespace S5

























theorem length_map {α β : Type} (f : α → β) (w : Word α) : length (w.map f) = length w := by
  induction w with
  | empty => rfl
  | snoc w g ih => change length (w.map f) + 1 = length w + 1; rw [ih]

theorem six_divisor_residue_supports (w : Word Nat) (hp : w.primeFactors)
    (hc : Nat.gcd (total natProduct w) 30 = 1) (hw : 6 ≤ length w) (u : Code30) :
    (∃ d : Nat, d ∣ total natProduct w ∧ d % 30 = residue30 u) ↔
      ∃ d : Nat, d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w ∧
        d % 30 = residue30 u := by
  calc
    _ ↔ fullSupport mod30Product (w.map encode30) u := (fullSupport_mod30_iff_divisor w hp hc u).symm
    _ ↔ properSupport mod30Product (w.map encode30) u := full_equals_proper_of_six _ (by rw [length_map]; exact hw) u
    _ ↔ _ := properSupport_mod30_iff_divisor w hp hc u

theorem p2m_local_six_for_factorization (w : Word Nat) (hp : w.primeFactors) (n : Nat)
    (hn : total natProduct w = n) (hc : Nat.gcd n 30 = 1) (hw : 6 ≤ length w) :
    ∀ u : Code30, (∃ d : Nat, d ∣ n ∧ d % 30 = residue30 u) ↔
      ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n ∧ d % 30 = residue30 u := by
  subst n
  exact six_divisor_residue_supports w hp hc hw

end S5
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (n : Nat),
      @Eq.{1} Nat (@Couret.total.{0} Nat Couret.natProduct w) n →
        @Eq.{1} Nat (Nat.gcd n (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
              (@Couret.S5.length Nat w) →
            ∀ (u : Couret.Code30),
              Iff
                (@Exists.{1} Nat fun d =>
                  And (@Dvd.dvd.{0} Nat Nat.instDvd d n)
                    (@Eq.{1} Nat
                      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                        (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                      (Couret.residue30 u)))
                (@Exists.{1} Nat fun d =>
                  And (@Dvd.dvd.{0} Nat Nat.instDvd d n)
                    (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
                      (And (@LT.lt.{0} Nat instLTNat d n)
                        (@Eq.{1} Nat
                          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                            (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                          (Couret.residue30 u))))) := @_root_.Couret.S5.p2m_local_six_for_factorization

