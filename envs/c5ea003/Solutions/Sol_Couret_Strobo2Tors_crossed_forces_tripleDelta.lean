-- Prove2me | solution 1 for Couret.Strobo2Tors.crossed_forces_tripleDelta
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:45:31.48906+00:00
-- url     : https://prove2.me/submissions/3dcc3c1f-648f-4ffc-acef-771f7ff3d452

import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_pair_coset_eq_iff
import Definitions.Def_Couret_RectangleFibres_2930a0e95467

/-!
STROBO-2TORS: normalized type-II crossed matching.

This theorem isolates the 3-torsion obstruction in the branch where the
singleton representatives have been aligned (d = b).
It proves equivalence at the level of equal two-point cosets, not yet
equivalence with SameSquare of arbitrary triple supports.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]



theorem p2m_local_crossed_forces_tripleDelta (a b c u : G)
    (hu : u + u = 0)
    (hfirst : pairSet (c + c) u = pairSet (a + b) u)
    (hsecond : pairSet (c + b) u = pairSet (a + a) u) :
    tripleDelta a b = 0 ∨ tripleDelta a b = u := by
  have hc : c + c = a + b ∨ c + c = (a + b) + u :=
    (pair_coset_eq_iff (a + b) (c + c) u hu).mp hfirst.symm
  have hcb : c + b = a + a ∨ c + b = (a + a) + u :=
    (pair_coset_eq_iff (a + a) (c + b) u hu).mp hsecond.symm
  have hdouble : (c + b) + (c + b) = (a + a) + (a + a) := by
    rcases hcb with h | h
    · rw [h]
    · rw [h]
      calc
        ((a + a) + u) + ((a + a) + u) =
            ((a + a) + (a + a)) + (u + u) := by abel
        _ = (a + a) + (a + a) := by rw [hu]; simp
  have htwo : (c + c) + (b + b) = (a + a) + (a + a) := by
    calc
      (c + c) + (b + b) = (c + b) + (c + b) := by abel
      _ = (a + a) + (a + a) := hdouble
  have hneg : -u = u := by
    calc
      -u = -u + (u + u) := by rw [hu]; simp
      _ = u := by abel
  rcases hc with h | h
  · left
    calc
      tripleDelta a b =
          ((c + c) + (b + b)) - ((a + a) + (a + a)) := by
        dsimp [tripleDelta]
        rw [h]
        abel
      _ = 0 := by rw [htwo]; simp
  · right
    calc
      tripleDelta a b =
          ((c + c) + (b + b)) - ((a + a) + (a + a)) - u := by
        dsimp [tripleDelta]
        rw [h]
        abel
      _ = -u := by rw [htwo]; simp
      _ = u := hneg



end Couret.Strobo2Tors

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [Fintype.{p2m_u_0} G] [inst_2 : DecidableEq.{p2m_u_0 + 1} G]
  (a b c u : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        u u)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
        (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            c c)
          u)
        (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a b)
          u) →
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
          (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              c b)
            u)
          (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              a a)
            u) →
        Or
          (@Eq.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.tripleDelta.{p2m_u_0} G inst a b)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
          (@Eq.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.tripleDelta.{p2m_u_0} G inst a b) u) := @_root_.Couret.Strobo2Tors.p2m_local_crossed_forces_tripleDelta

