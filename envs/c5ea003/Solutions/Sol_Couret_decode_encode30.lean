-- Prove2me | solution 1 for Couret.decode_encode30
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:34.977846+00:00
-- url     : https://prove2.me/submissions/c951e33b-6afd-402c-b148-b9fbdad09120

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





theorem decode_unit_residue : ∀ r : Fin 30, Nat.gcd r.val 30 = 1 →
    residue30 (rawCode30 r.val) = r.val := by decide

theorem p2m_local_decode_encode30 (n : Nat) (hn : Nat.gcd n 30 = 1) :
    residue30 (encode30 n) = n % 30 := by
  have hm : Nat.gcd (n % 30) 30 = 1 := by
    rw [← Nat.gcd_rec 30 n, Nat.gcd_comm]
    exact hn
  exact decode_unit_residue ⟨n % 30, Nat.mod_lt _ (by decide)⟩ hm

































end Couret


theorem solution : ∀ (n : Nat),
  @Eq.{1} Nat (Nat.gcd n (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (Couret.residue30 (Couret.encode30 n))
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) n
        (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := @_root_.Couret.p2m_local_decode_encode30

