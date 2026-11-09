-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Lifts.four_orbit_lift
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:31.170206+00:00
-- url     : https://prove2.me/submissions/159ac82c-a797-4096-b719-5b5876132e80

import Definitions.Def_Couret_OrbitLiftModels_210387863d55
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_order_four_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_projected_step_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_reconstruct_pair_fibre
import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Catalogue.Orbits Couret.InterIA.Parity







theorem p2m_local_four_orbit_lift (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (a b c d : ZMod (2*m))
    (hU : S \ T=fibre (m : ZMod (2*m)) a)
    (hV : T \ S=fibre (m : ZMod (2*m)) b) (hC : S ∩ T={c,d})
    (ho : addOrderOf (projection m (b-a))=4)
    (hc : projection m c=projection m a+2 • projection m (b-a))
    (hd : projection m d=projection m a+3 • projection m (b-a)) : FourLift m S T := by
  let r := b-a
  have hr : 4 • r=(m : ZMod (2*m)) := projected_order_four_lift m hm r ho
  have hb : b=a+r := by dsimp [r]; abel
  have hcl : c=a+2 • r ∨ c=a+6 • r := by
    rcases projected_step_lift m hm a c r 2 hc with he|he
    · exact Or.inl he
    · right
      calc c=a+2 • r+m := he
           _=a+6 • r := by rw [← hr,show (6 : ℕ)=2+4 from rfl,add_nsmul]; abel
  have hdl : d=a+3 • r ∨ d=a+7 • r := by
    rcases projected_step_lift m hm a d r 3 hd with he|he
    · exact Or.inl he
    · right
      calc d=a+3 • r+m := he
           _=a+7 • r := by rw [← hr,show (7 : ℕ)=3+4 from rfl,add_nsmul]; abel
  have hSe := reconstruct_pair_fibre m S T a c d hU hC
  have hTe := reconstruct_pair_fibre m T S b c d hV (by rw [inter_comm]; exact hC)
  have h5 : a+r+4 • r=a+5 • r := by
    rw [show (5 : ℕ)=1+4 from rfl,add_nsmul,one_nsmul]
    abel
  exact ⟨a,r,c,d,hr,hcl,hdl,by simpa only [← hr] using hSe,
    by simpa only [hb,← hr,h5] using hTe⟩

end Couret.InterIA.Catalogue.Lifts

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (S T :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
      (a b c d :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
      @Eq.{1}
          (Finset.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
          (@SDiff.sdiff.{0}
            (Finset.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
            (@Finset.instSDiff.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (ZMod.decidableEq
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
            S T)
          (@Couret.InterIA.Fibres.fibre.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@Ring.toAddCommGroup.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@CommRing.toRing.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (ZMod.commRing
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
            (ZMod.decidableEq
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@Nat.cast.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@AddMonoidWithOne.toNatCast.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Ring.toAddGroupWithOne.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommRing.toRing.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
              m)
            a) →
        @Eq.{1}
            (Finset.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
            (@SDiff.sdiff.{0}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (@Finset.instSDiff.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              T S)
            (@Couret.InterIA.Fibres.fibre.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@Ring.toAddCommGroup.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@CommRing.toRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (ZMod.commRing
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
              (ZMod.decidableEq
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@Nat.cast.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@AddMonoidWithOne.toNatCast.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@Ring.toAddGroupWithOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@CommRing.toRing.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.commRing
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
                m)
              b) →
          @Eq.{1}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (@Inter.inter.{0}
                (Finset.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                (@Finset.instInter.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (ZMod.decidableEq
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                S T)
              (@Insert.insert.{0, 0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (Finset.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                (@Finset.instInsert.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (ZMod.decidableEq
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                c
                (@Singleton.singleton.{0, 0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (Finset.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                  (@Finset.instSingleton.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                  d)) →
            @Eq.{1} Nat
                (@addOrderOf.{0} (ZMod m)
                  (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                      (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))
                  (@DFunLike.coe.{1, 1, 1}
                    (@RingHom.{0, 0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod m)
                      (@Semiring.toNonAssocSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                      (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                        (@CommSemiring.toSemiring.{0} (ZMod m)
                          (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (fun x => ZMod m)
                    (@RingHom.instFunLike.{0, 0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod m)
                      (@Semiring.toNonAssocSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                      (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                        (@CommSemiring.toSemiring.{0} (ZMod m)
                          (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                    (Couret.InterIA.Projection.projection m)
                    (@HSub.hSub.{0, 0, 0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (@instHSub.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (@SubNegMonoid.toSub.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@AddGroup.toSubNegMonoid.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@AddGroupWithOne.toAddGroup.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toRing.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))))
                      b a)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              @Eq.{1} (ZMod m)
                  (@DFunLike.coe.{1, 1, 1}
                    (@RingHom.{0, 0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod m)
                      (@Semiring.toNonAssocSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                      (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                        (@CommSemiring.toSemiring.{0} (ZMod m)
                          (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (fun x => ZMod m)
                    (@RingHom.instFunLike.{0, 0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod m)
                      (@Semiring.toNonAssocSemiring.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                      (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                        (@CommSemiring.toSemiring.{0} (ZMod m)
                          (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                    (Couret.InterIA.Projection.projection m) c)
                  (@HAdd.hAdd.{0, 0, 0} (ZMod m) (ZMod m) (ZMod m)
                    (@instHAdd.{0} (ZMod m)
                      (@Distrib.toAdd.{0} (ZMod m)
                        (@instDistribOfSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m))))))
                    (@DFunLike.coe.{1, 1, 1}
                      (@RingHom.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod m)
                        (@Semiring.toNonAssocSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                        (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (fun x => ZMod m)
                      (@RingHom.instFunLike.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod m)
                        (@Semiring.toNonAssocSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                        (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                      (Couret.InterIA.Projection.projection m) a)
                    (@HSMul.hSMul.{0, 0, 0} Nat (ZMod m) (ZMod m)
                      (@instHSMul.{0, 0} Nat (ZMod m)
                        (@AddMonoid.toNSMul.{0} (ZMod m)
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                              (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@DFunLike.coe.{1, 1, 1}
                        (@RingHom.{0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod m)
                          (@Semiring.toNonAssocSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommSemiring.toSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommRing.toCommSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (ZMod.commRing
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                          (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (fun x => ZMod m)
                        (@RingHom.instFunLike.{0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod m)
                          (@Semiring.toNonAssocSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommSemiring.toSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommRing.toCommSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (ZMod.commRing
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                          (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                        (Couret.InterIA.Projection.projection m)
                        (@HSub.hSub.{0, 0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@instHSub.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@SubNegMonoid.toSub.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@AddGroup.toSubNegMonoid.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@AddGroupWithOne.toAddGroup.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (@Ring.toAddGroupWithOne.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                    (@CommRing.toRing.{0}
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                      (ZMod.commRing
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))))
                          b a)))) →
                @Eq.{1} (ZMod m)
                    (@DFunLike.coe.{1, 1, 1}
                      (@RingHom.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod m)
                        (@Semiring.toNonAssocSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                        (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (fun x => ZMod m)
                      (@RingHom.instFunLike.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod m)
                        (@Semiring.toNonAssocSemiring.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (ZMod.commRing
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                        (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                          (@CommSemiring.toSemiring.{0} (ZMod m)
                            (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                      (Couret.InterIA.Projection.projection m) d)
                    (@HAdd.hAdd.{0, 0, 0} (ZMod m) (ZMod m) (ZMod m)
                      (@instHAdd.{0} (ZMod m)
                        (@Distrib.toAdd.{0} (ZMod m)
                          (@instDistribOfSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m))))))
                      (@DFunLike.coe.{1, 1, 1}
                        (@RingHom.{0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod m)
                          (@Semiring.toNonAssocSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommSemiring.toSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommRing.toCommSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (ZMod.commRing
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                          (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (fun x => ZMod m)
                        (@RingHom.instFunLike.{0, 0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (ZMod m)
                          (@Semiring.toNonAssocSemiring.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@CommSemiring.toSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommRing.toCommSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (ZMod.commRing
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                          (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                            (@CommSemiring.toSemiring.{0} (ZMod m)
                              (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                        (Couret.InterIA.Projection.projection m) a)
                      (@HSMul.hSMul.{0, 0, 0} Nat (ZMod m) (ZMod m)
                        (@instHSMul.{0, 0} Nat (ZMod m)
                          (@AddMonoid.toNSMul.{0} (ZMod m)
                            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                                (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                  (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@DFunLike.coe.{1, 1, 1}
                          (@RingHom.{0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod m)
                            (@Semiring.toNonAssocSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                            (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                              (@CommSemiring.toSemiring.{0} (ZMod m)
                                (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (fun x => ZMod m)
                          (@RingHom.instFunLike.{0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod m)
                            (@Semiring.toNonAssocSemiring.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@CommSemiring.toSemiring.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@CommRing.toCommSemiring.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (ZMod.commRing
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))
                            (@Semiring.toNonAssocSemiring.{0} (ZMod m)
                              (@CommSemiring.toSemiring.{0} (ZMod m)
                                (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))
                          (Couret.InterIA.Projection.projection m)
                          (@HSub.hSub.{0, 0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@instHSub.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@SubNegMonoid.toSub.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@AddGroup.toSubNegMonoid.{0}
                                  (ZMod
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                  (@AddGroupWithOne.toAddGroup.{0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                    (@Ring.toAddGroupWithOne.{0}
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                      (@CommRing.toRing.{0}
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (ZMod.commRing
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))))
                            b a)))) →
                  Couret.InterIA.Catalogue.Lifts.FourLift m S T := @_root_.Couret.InterIA.Catalogue.Lifts.p2m_local_four_orbit_lift

