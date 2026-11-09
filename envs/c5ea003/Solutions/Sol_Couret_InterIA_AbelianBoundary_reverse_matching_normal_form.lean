-- Prove2me | solution 1 for Couret.InterIA.AbelianBoundary.reverse_matching_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:28.569602+00:00
-- url     : https://prove2.me/submissions/f47ab643-5d24-4d3d-a1ce-9a6803796150

import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

/- Algebraic consequences of the surviving matching.
Compiled locally; the full parity-to-matching reduction is separate. -/
set_option autoImplicit false

namespace Couret.InterIA.AbelianBoundary

variable {H : Type*} [AddCommGroup H]

theorem p2m_local_reverse_matching_normal_form
    (a b c d e f : H)
    (ha : a = e + f)
    (hab : a + b = f) (hac : a + c = e) (hbc : b + c = d) :
    a + b + c = 0 ∧ d = -a ∧ e = -b ∧ f = -c := by
  have hs : a + b + c = 0 := by
    calc
      a + b + c = ((a + c) + (a + b)) - a := by abel
      _ = (e + f) - a := by rw [hac, hab]
      _ = a - a := by rw [← ha]
      _ = 0 := sub_self a
  refine ⟨hs, ?_, ?_, ?_⟩
  · calc
      d = (a + b + c) - a := by rw [← hbc]; abel
      _ = -a := by rw [hs]; simp
  · calc
      e = (a + b + c) - b := by rw [← hac]; abel
      _ = -b := by rw [hs]; simp
  · calc
      f = (a + b + c) - c := by rw [← hab]; abel
      _ = -c := by rw [hs]; simp



end Couret.InterIA.AbelianBoundary


universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] (a b c d e f : H),
  @Eq.{p2m_u_0 + 1} H a
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
        (@instHAdd.{p2m_u_0} H
          (@AddCommMagma.toAdd.{p2m_u_0} H
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
        e f) →
    @Eq.{p2m_u_0 + 1} H
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
          (@instHAdd.{p2m_u_0} H
            (@AddCommMagma.toAdd.{p2m_u_0} H
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
          a b)
        f →
      @Eq.{p2m_u_0 + 1} H
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
            (@instHAdd.{p2m_u_0} H
              (@AddCommMagma.toAdd.{p2m_u_0} H
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
            a c)
          e →
        @Eq.{p2m_u_0 + 1} H
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
              (@instHAdd.{p2m_u_0} H
                (@AddCommMagma.toAdd.{p2m_u_0} H
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
              b c)
            d →
          And
            (@Eq.{p2m_u_0 + 1} H
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
                (@instHAdd.{p2m_u_0} H
                  (@AddCommMagma.toAdd.{p2m_u_0} H
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
                  (@instHAdd.{p2m_u_0} H
                    (@AddCommMagma.toAdd.{p2m_u_0} H
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
                  a b)
                c)
              (@OfNat.ofNat.{p2m_u_0} H (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} H
                  (@NegZeroClass.toZero.{p2m_u_0} H
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst))))))))
            (And
              (@Eq.{p2m_u_0 + 1} H d
                (@Neg.neg.{p2m_u_0} H
                  (@NegZeroClass.toNeg.{p2m_u_0} H
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst)))))
                  a))
              (And
                (@Eq.{p2m_u_0 + 1} H e
                  (@Neg.neg.{p2m_u_0} H
                    (@NegZeroClass.toNeg.{p2m_u_0} H
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst)))))
                    b))
                (@Eq.{p2m_u_0 + 1} H f
                  (@Neg.neg.{p2m_u_0} H
                    (@NegZeroClass.toNeg.{p2m_u_0} H
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst)))))
                    c)))) := @_root_.Couret.InterIA.AbelianBoundary.p2m_local_reverse_matching_normal_form

