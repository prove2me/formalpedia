-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Periods.collision_periods
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:05.41956+00:00
-- url     : https://prove2.me/submissions/8f0f57dc-4f03-4a03-8be9-845578470761

import Definitions.Def_Couret_QuotientPeriods_cf8d74422994
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
import Theorems.Thm_Couret_InterIA_Catalogue_Periods_residual_periods
import Theorems.Thm_Couret_InterIA_Catalogue_normal_form_quotient_invariant
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Periods
open Finset Couret.InterIA.Catalogue Couret.InterIA.Parity Couret.InterIA.Projection
variable {G : Type*} [AddCommGroup G] [DecidableEq G]















/-- The quotient shift of actual normal-form supports has order two or four. -/
theorem normal_form_periods (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m)))
    (hn : Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∃ a b, (addOrderOf (projection m (b-a))=2 ∨ addOrderOf (projection m (b-a))=4) ∧
      residual m (S ∩ T) a b=A (projection m (b-a))*residual m (S ∩ T) a b ∧
      (residual m (S ∩ T) a b).sum (fun _ n => n)=4 ∧
      (∀ z, 0 ≤ (residual m (S ∩ T) a b).coeff z) := by
  obtain ⟨a,b,hd,hi,hmass,hpos⟩ := normal_form_quotient_invariant m hm S T hn hsq
  exact ⟨a,b,residual_periods m (S ∩ T) hn.1 a b _ hd hi,hi,hmass,hpos⟩

/-- Direct raccord from the initial non-affine collision to periods two or four. -/
theorem p2m_local_collision_periods (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S (T.image (fun x => x+t)) ∧
      ∃ a b, (addOrderOf (projection m (b-a))=2 ∨ addOrderOf (projection m (b-a))=4) ∧
        residual m (S ∩ T.image (fun x => x+t)) a b=
          A (projection m (b-a))*residual m (S ∩ T.image (fun x => x+t)) a b ∧
        (residual m (S ∩ T.image (fun x => x+t)) a b).sum (fun _ n => n)=4 ∧
        (∀ z, 0 ≤ (residual m (S ∩ T.image (fun x => x+t)) a b).coeff z) := by
  obtain ⟨t,ht,hn⟩ := Couret.InterIA.NormalForm.even_cyclic_L4 m hm S T hS hT hsq hnaff
  have he : ∀ z, orderedSquare S z=orderedSquare (T.image (fun x => x+t)) z := by
    intro z
    rcases ht with ht|ht
    · simpa only [ht,add_zero,Finset.image_id'] using hsq z
    · rw [ht,Couret.InterIA.Translation.two_torsion_translation_preserves_square T m
        (Couret.InterIA.L4.half_add_half m)]
      exact hsq z
  exact ⟨t,ht,hn,normal_form_periods m hm S (T.image (fun x => x+t)) hn he⟩

end Couret.InterIA.Catalogue.Periods

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (S T :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
      @Eq.{1} Nat
          (@Finset.card.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            S)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Eq.{1} Nat
            (@Finset.card.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              T)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          (∀
              (z :
                ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
              @Eq.{1} Nat
                (@Couret.InterIA.Parity.orderedSquare.{0}
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
                  S z)
                (@Couret.InterIA.Parity.orderedSquare.{0}
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
                  T z)) →
            Not
                (@Couret.InterIA.NormalForm.AffineEquivalent
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                  S T) →
              @Exists.{1}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                fun t =>
                And
                  (Or
                    (@Eq.{1}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      t
                      (@OfNat.ofNat.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (nat_lit 0)
                        (@Zero.toOfNat0.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                          (@MulZeroClass.toZero.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@instMulZeroClassOfSemiring.{0}
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))))))
                    (@Eq.{1}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      t
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
                        m)))
                  (And
                    (@Couret.InterIA.NormalForm.Normal.{0}
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
                      S
                      (@Finset.image.{0, 0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.decidableEq
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (fun x =>
                          @HAdd.hAdd.{0, 0, 0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                            (@instHAdd.{0}
                              (ZMod
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                              (@Distrib.toAdd.{0}
                                (ZMod
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                (@instDistribOfSemiring.{0}
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
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))))
                            x t)
                        T))
                    (@Exists.{1}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      fun a =>
                      @Exists.{1}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        fun b =>
                        And
                          (Or
                            (@Eq.{1} Nat
                              (@addOrderOf.{0} (ZMod m)
                                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                                    (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                      (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))
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
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    m))))))))
                                    b a)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Eq.{1} Nat
                              (@addOrderOf.{0} (ZMod m)
                                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                                    (@Ring.toAddGroupWithOne.{0} (ZMod m)
                                      (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))
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
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    m))))))))
                                    b a)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                          (And
                            (@Eq.{1} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                              (Couret.InterIA.Catalogue.residual m
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
                                  S
                                  (@Finset.image.{0, 0}
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                    (ZMod
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                    (ZMod.decidableEq
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                    (fun x =>
                                      @HAdd.hAdd.{0, 0, 0}
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (@instHAdd.{0}
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                          (@Distrib.toAdd.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (@instDistribOfSemiring.{0}
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
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      m)))))))
                                        x t)
                                    T))
                                a b)
                              (@HMul.hMul.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                                (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                                (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                                (@instHMul.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                                  (@AddMonoidAlgebra.instMul.{0, 0} Int (ZMod m) Int.instSemiring
                                    (@Distrib.toAdd.{0} (ZMod m)
                                      (@instDistribOfSemiring.{0} (ZMod m)
                                        (@CommSemiring.toSemiring.{0} (ZMod m)
                                          (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
                                (@Couret.InterIA.Catalogue.A m
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
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      m))))))))
                                      b a)))
                                (Couret.InterIA.Catalogue.residual m
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
                                    S
                                    (@Finset.image.{0, 0}
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                      (ZMod
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                      (ZMod.decidableEq
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                      (fun x =>
                                        @HAdd.hAdd.{0, 0, 0}
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                          (ZMod
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                          (@instHAdd.{0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (@Distrib.toAdd.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                              (@instDistribOfSemiring.{0}
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
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        m))
                                                    (ZMod.commRing
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        m)))))))
                                          x t)
                                      T))
                                  a b)))
                            (And
                              (@Eq.{1} Int
                                (@Finsupp.sum.{0, 0, 0} (ZMod m) Int Int
                                  (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
                                  Int.instAddCommMonoid
                                  (Couret.InterIA.Catalogue.residual m
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
                                      S
                                      (@Finset.image.{0, 0}
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (ZMod
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (ZMod.decidableEq
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                        (fun x =>
                                          @HAdd.hAdd.{0, 0, 0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (@instHAdd.{0}
                                              (ZMod
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                              (@Distrib.toAdd.{0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                                (@instDistribOfSemiring.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                                  (@CommSemiring.toSemiring.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        m))
                                                    (@CommRing.toCommSemiring.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          m))
                                                      (ZMod.commRing
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          m)))))))
                                            x t)
                                        T))
                                    a b)
                                  fun x n => n)
                                (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))
                              (∀ (z : ZMod m),
                                @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@DFunLike.coe.{1, 1, 1}
                                    (@Finsupp.{0, 0} (ZMod m) Int
                                      (@MulZeroClass.toZero.{0} Int
                                        (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
                                    (ZMod m) (fun x => Int)
                                    (@Finsupp.instFunLike.{0, 0} (ZMod m) Int
                                      (@MulZeroClass.toZero.{0} Int
                                        (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
                                    (@AddMonoidAlgebra.coeff.{0, 0} Int (ZMod m) Int.instSemiring
                                      (Couret.InterIA.Catalogue.residual m
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
                                          S
                                          (@Finset.image.{0, 0}
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (ZMod
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (ZMod.decidableEq
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                            (fun x =>
                                              @HAdd.hAdd.{0, 0, 0}
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                                (ZMod
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                                (@instHAdd.{0}
                                                  (ZMod
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                                  (@Distrib.toAdd.{0}
                                                    (ZMod
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        m))
                                                    (@instDistribOfSemiring.{0}
                                                      (ZMod
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          m))
                                                      (@CommSemiring.toSemiring.{0}
                                                        (ZMod
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            m))
                                                        (@CommRing.toCommSemiring.{0}
                                                          (ZMod
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              m))
                                                          (ZMod.commRing
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              m)))))))
                                                x t)
                                            T))
                                        a b))
                                    z)))))) := @_root_.Couret.InterIA.Catalogue.Periods.p2m_local_collision_periods

