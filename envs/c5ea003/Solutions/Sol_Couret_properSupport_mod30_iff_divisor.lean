-- Prove2me | solution 1 for Couret.properSupport_mod30_iff_divisor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:04:24.289194+00:00
-- url     : https://prove2.me/submissions/9565a149-cc0d-49d2-b001-e69cac7f9b93

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_properSupport_iff_nontrivial_divisor
import Theorems.Thm_Couret_properSupport_map_iff
import Definitions.Def_Couret_DivisorCompleteness_e4011d047800

/-!
COU-87 S2M, 2026-10-30: the exact bridge from natural divisors to the
eight-letter modulo-30 automaton. Prime occurrences need not be distinct.
No finite 147-state / 101-class table is imported here.
-/

universe v
namespace Couret



namespace Choice











end Choice













theorem coprime30Factors_of_total (w : Word Nat)
    (hw : Nat.gcd (total natProduct w) 30 = 1) : w.coprime30Factors := by
  induction w with
  | empty => exact True.intro
  | snoc w p ih =>
    have htail : total natProduct w ∣ total natProduct (.snoc w p) := ⟨p, rfl⟩
    have hlast : p ∣ total natProduct (.snoc w p) := by
      refine ⟨total natProduct w, ?_⟩
      exact Nat.mul_comm _ _
    exact ⟨ih (coprime30_of_dvd htail hw), coprime30_of_dvd hlast hw⟩













theorem p2m_local_properSupport_mod30_iff_divisor (w : Word Nat) (hp : w.primeFactors)
    (hc : Nat.gcd (total natProduct w) 30 = 1) (u : Code30) :
    properSupport mod30Product (w.map encode30) u ↔
      ∃ d : Nat, d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w ∧
        d % 30 = residue30 u := by
  rw [properSupport_map_iff w (coprime30Factors_of_total w hc)]
  constructor
  · rintro ⟨d, hd, hr⟩
    rcases (properSupport_iff_nontrivial_divisor w hp d).mp hd with ⟨hdiv, h1, hn⟩
    exact ⟨d, hdiv, h1, hn, hr⟩
  · rintro ⟨d, hdiv, h1, hn, hr⟩
    exact ⟨d, (properSupport_iff_nontrivial_divisor w hp d).mpr ⟨hdiv, h1, hn⟩, hr⟩













end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    @Eq.{1} Nat
        (Nat.gcd (@Couret.total.{0} Nat Couret.natProduct w)
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      ∀ (u : Couret.Code30),
        Iff
          (@Couret.properSupport.{0} Couret.Code30 Couret.mod30Product
            (@Couret.Word.map.{0} Nat Couret.Code30 Couret.encode30 w) u)
          (@Exists.{1} Nat fun d =>
            And (@Dvd.dvd.{0} Nat Nat.instDvd d (@Couret.total.{0} Nat Couret.natProduct w))
              (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
                (And (@LT.lt.{0} Nat instLTNat d (@Couret.total.{0} Nat Couret.natProduct w))
                  (@Eq.{1} Nat
                    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                    (Couret.residue30 u))))) := @_root_.Couret.p2m_local_properSupport_mod30_iff_divisor

