-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.mixed_count_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:28.335341+00:00
-- url     : https://prove2.me/submissions/9d1e3b6b-8265-49b6-98e4-9dd28581bd62

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportLeft
import Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportRight
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



theorem p2m_local_mixed_count_cancellation (x : Fin 6 → G) (hd : SevenDistinct x)
    (hx : MixedDoubles x)
    (hs : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z) :
    (sumTermsLeft x ++ [x 0+x 0]).Perm (sumTermsRight x ++ [x 3+x 3]) := by
  apply List.perm_iff_count.mpr
  intro z
  have h := hs z
  rw [square_supportLeft x hd,square_supportRight x hd] at h
  rcases hx with ⟨h0,h1,h2⟩
  rw [← h0,← h1,h2] at h
  simp only [List.count_cons,List.count_nil,beq_iff_eq,add_zero] at h
  simp only [List.count_append,List.count_cons,List.count_nil,beq_iff_eq,add_zero]
  omega

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    @Couret.InterIA.SingletonNecessity.MixedDoubles.{p2m_u_0} G inst x →
      (∀ (z : G),
          @Eq.{1} Nat
            (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
              (@Couret.InterIA.SingletonNecessity.supportLeft.{p2m_u_0} G inst inst_1 x) z)
            (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
              (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 x) z)) →
        @List.Perm.{p2m_u_0} G
          (@HAppend.hAppend.{p2m_u_0, p2m_u_0, p2m_u_0} (List.{p2m_u_0} G) (List.{p2m_u_0} G) (List.{p2m_u_0} G)
            (@instHAppendOfAppend.{p2m_u_0} (List.{p2m_u_0} G) (@List.instAppend.{p2m_u_0} G))
            (@Couret.InterIA.SingletonNecessity.sumTermsLeft.{p2m_u_0} G inst x)
            (@List.cons.{p2m_u_0} G
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0))))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (nat_lit 0)))))
              (@List.nil.{p2m_u_0} G)))
          (@HAppend.hAppend.{p2m_u_0, p2m_u_0, p2m_u_0} (List.{p2m_u_0} G) (List.{p2m_u_0} G) (List.{p2m_u_0} G)
            (@instHAppendOfAppend.{p2m_u_0} (List.{p2m_u_0} G) (@List.instAppend.{p2m_u_0} G))
            (@Couret.InterIA.SingletonNecessity.sumTermsRight.{p2m_u_0} G inst x)
            (@List.cons.{p2m_u_0} G
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 3)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 3))))
                (x
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 3)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (nat_lit 3)))))
              (@List.nil.{p2m_u_0} G))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_mixed_count_cancellation

