-- Prove2me | solution 1 for Couret.Strobo2Tors.rectangle_equal_double_values
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:57.603712+00:00
-- url     : https://prove2.me/submissions/906e9287-8dbe-4a40-93fd-e574c91636fd

import Definitions.Def_Couret_RectangleFibres_2930a0e95467
import Mathlib
import Definitions.Def_Couret_Prelude_5b3cc8c481fb

/-!
STROBO type-II rectangle: intrinsic recovery of the two doubled fibres.
This file does not prove the full universal collision classification.

Given u+u=0 and doubleValue x != doubleValue y, the four-point
rectangle {x,x+u,y,y+u} splits canonically by the doubling map into
the two sets {x,x+u} and {y,y+u}.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]







theorem doubleValue_add_torsion (x u : G) (hu : u + u = 0) :
    doubleValue (x + u) = doubleValue x := by
  dsimp [doubleValue]
  calc
    (x + u) + (x + u) = (x + x) + (u + u) := by abel
    _ = x + x := by rw [hu]; simp







theorem rectangle_double_image (x y u : G) (hu : u + u = 0) :
    (rectangleSet x y u).image doubleValue =
      ({doubleValue x, doubleValue y} : Finset G) := by
  calc
    (rectangleSet x y u).image doubleValue =
        (pairSet x u).image doubleValue ∪ (pairSet y u).image doubleValue := by
      simp [rectangleSet, Finset.image_union]
    _ = {doubleValue x, doubleValue y} := by
      simp [pairSet, doubleValue_add_torsion x u hu,
        doubleValue_add_torsion y u hu]

theorem p2m_local_rectangle_equal_double_values (x y u a b v : G)
    (hu : u + u = 0) (hv : v + v = 0)
    (heq : rectangleSet x y u = rectangleSet a b v) :
    ({doubleValue x, doubleValue y} : Finset G) =
      ({doubleValue a, doubleValue b} : Finset G) := by
  calc
    ({doubleValue x, doubleValue y} : Finset G) =
        (rectangleSet x y u).image doubleValue :=
      (rectangle_double_image x y u hu).symm
    _ = (rectangleSet a b v).image doubleValue := by rw [heq]
    _ = ({doubleValue a, doubleValue b} : Finset G) :=
      rectangle_double_image a b v hv

end Couret.Strobo2Tors

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [Fintype.{p2m_u_0} G] [inst_2 : DecidableEq.{p2m_u_0 + 1} G]
  (x y u a b v : G),
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
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          v v)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.Strobo2Tors.rectangleSet.{p2m_u_0} G inst inst_2 x y u)
          (@Couret.Strobo2Tors.rectangleSet.{p2m_u_0} G inst inst_2 a b v) →
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_2)
            (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst x)
            (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
              (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst y)))
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_2)
            (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst a)
            (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
              (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst b))) := @_root_.Couret.Strobo2Tors.p2m_local_rectangle_equal_double_values

