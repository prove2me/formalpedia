-- Prove2me | solution 1 for Couret.proper_divisor_can_have_residue_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:19.485202+00:00
-- url     : https://prove2.me/submissions/475de715-468f-41cf-aa8a-73c5fde0eb43

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







































theorem p2m_local_proper_divisor_can_have_residue_one :
    properSupport mod30Product
      ((Word.snoc (.snoc .empty 31) 31).map encode30) (0, 0) := by
  refine ⟨.skip (.take .empty (encode30 31)) (encode30 31), True.intro, True.intro, ?_⟩
  decide

end Couret


theorem solution : @Couret.properSupport.{0} Couret.Code30 Couret.mod30Product
  (@Couret.Word.map.{0} Nat Couret.Code30 Couret.encode30
    (@Couret.Word.snoc.{0} Nat
      (@Couret.Word.snoc.{0} Nat (@Couret.Word.empty.{0} Nat)
        (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
      (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))))
  (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))) := @_root_.Couret.p2m_local_proper_divisor_can_have_residue_one

