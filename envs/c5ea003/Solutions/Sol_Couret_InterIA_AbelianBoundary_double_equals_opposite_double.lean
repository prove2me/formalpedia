-- Prove2me | solution 1 for Couret.InterIA.AbelianBoundary.double_equals_opposite_double
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:22.82664+00:00
-- url     : https://prove2.me/submissions/ff694f7a-dfa2-4ddd-8bda-fbacaeab948d

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



theorem p2m_local_double_equals_opposite_double (a d : H)
    (hd : d = -a) (hh : a + a = d + d) :
    (a + a) + (a + a) = 0 := by
  calc
    (a + a) + (a + a) = (a + a) + (d + d) :=
      congrArg (fun z : H => (a + a) + z) hh
    _ = 0 := by rw [hd]; abel

end Couret.InterIA.AbelianBoundary


universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] (a d : H),
  @Eq.{p2m_u_0 + 1} H d
      (@Neg.neg.{p2m_u_0} H
        (@NegZeroClass.toNeg.{p2m_u_0} H
          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst)))))
        a) →
    @Eq.{p2m_u_0 + 1} H
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
          (@instHAdd.{p2m_u_0} H
            (@AddCommMagma.toAdd.{p2m_u_0} H
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
          a a)
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
          (@instHAdd.{p2m_u_0} H
            (@AddCommMagma.toAdd.{p2m_u_0} H
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
          d d) →
      @Eq.{p2m_u_0 + 1} H
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
          (@instHAdd.{p2m_u_0} H
            (@AddCommMagma.toAdd.{p2m_u_0} H
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
            (@instHAdd.{p2m_u_0} H
              (@AddCommMagma.toAdd.{p2m_u_0} H
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
            a a)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} H H H
            (@instHAdd.{p2m_u_0} H
              (@AddCommMagma.toAdd.{p2m_u_0} H
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} H
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} H (@AddCommGroup.toAddCommMonoid.{p2m_u_0} H inst)))))
            a a))
        (@OfNat.ofNat.{p2m_u_0} H (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} H
            (@NegZeroClass.toZero.{p2m_u_0} H
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} H
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} H
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} H
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} H inst))))))) := @_root_.Couret.InterIA.AbelianBoundary.p2m_local_double_equals_opposite_double

