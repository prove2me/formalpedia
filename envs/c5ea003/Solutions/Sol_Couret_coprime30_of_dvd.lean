-- Prove2me | solution 1 for Couret.coprime30_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:13.336022+00:00
-- url     : https://prove2.me/submissions/d951124f-81b9-4a58-aefb-030b451a6687

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
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









theorem p2m_local_coprime30_of_dvd {d n : Nat} (hd : d ∣ n)
    (hn : Nat.gcd n 30 = 1) : Nat.gcd d 30 = 1 := by
  apply Nat.gcd_eq_one_iff.mpr
  intro c hcd hc30
  exact Nat.gcd_eq_one_iff.mp hn c (Nat.dvd_trans hcd hd) hc30































end Couret


theorem solution : ∀ {d n : Nat},
  @Dvd.dvd.{0} Nat Nat.instDvd d n →
    @Eq.{1} Nat (Nat.gcd n (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (Nat.gcd d (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.p2m_local_coprime30_of_dvd

