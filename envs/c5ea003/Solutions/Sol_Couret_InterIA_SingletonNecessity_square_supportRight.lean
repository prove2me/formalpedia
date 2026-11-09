-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.square_supportRight
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:07:11.97897+00:00
-- url     : https://prove2.me/submissions/6fe63a34-ff64-4877-ab17-e84942785f4b

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



theorem square_four (a b c z : G) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orderedSquare ({0,a,b,c} : Finset G) z =
      (if 0=z then 1 else 0) + [a+a,b+b,c+c].count z +
      2 * [a,b,c,a+b,a+c,b+c].count z := by
  have h0 : (0:G) ∉ ({a,b,c}:Finset G) := by simp [Ne.symm ha,Ne.symm hb,Ne.symm hc]
  have h1 : a ∉ ({b,c}:Finset G) := by simp [hab,hac]
  have h2 : b ∉ ({c}:Finset G) := by simp [hbc]
  simp only [orderedSquare,Finset.sum_insert h0,Finset.sum_insert h1,
    Finset.sum_insert h2,Finset.sum_singleton,zero_add,add_zero,
    List.count_cons,List.count_nil,beq_iff_eq,add_comm]
  omega







theorem p2m_local_square_supportRight (x : Fin 6 → G) (hd : SevenDistinct x) (z : G) :
    orderedSquare (supportRight x) z =
      (if 0=z then 1 else 0) + [x 3+x 3,x 4+x 4,x 5+x 5].count z +
      2 * (sumTermsRight x).count z := by
  have hi := sevenDistinct_injective x hd
  exact square_four _ _ _ _ (nonzero_of_distinctLabels x hd 3)
    (nonzero_of_distinctLabels x hd 4) (nonzero_of_distinctLabels x hd 5)
    (fun h => by have := hi h; contradiction)
    (fun h => by have := hi h; contradiction)
    (fun h => by have := hi h; contradiction)



end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    ∀ (z : G),
      @Eq.{1} Nat
        (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
          (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 x) z)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@ite.{1} Nat
              (@Eq.{p2m_u_0 + 1} G
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                z)
              (inst_1
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
                z)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@List.count.{p2m_u_0} G (@instBEqOfDecidableEq.{p2m_u_0} G inst_1) z
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
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (nat_lit 3))))
                  (x
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 3)
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (nat_lit 3)))))
                (@List.cons.{p2m_u_0} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 4)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (nat_lit 4))))
                    (x
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 4)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (nat_lit 4)))))
                  (@List.cons.{p2m_u_0} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (x
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                          (nat_lit 5)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (nat_lit 5))))
                      (x
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                          (nat_lit 5)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (nat_lit 5)))))
                    (@List.nil.{p2m_u_0} G))))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@List.count.{p2m_u_0} G (@instBEqOfDecidableEq.{p2m_u_0} G inst_1) z
              (@Couret.InterIA.SingletonNecessity.sumTermsRight.{p2m_u_0} G inst x)))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_square_supportRight

