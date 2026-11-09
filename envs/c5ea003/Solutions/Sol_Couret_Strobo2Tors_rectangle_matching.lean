-- Prove2me | solution 1 for Couret.Strobo2Tors.rectangle_matching
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:59:53.316205+00:00
-- url     : https://prove2.me/submissions/232516e4-6359-4cec-863b-b9f0f65a4519

import Definitions.Def_Couret_RectangleFibres_2930a0e95467
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_rectangle_equal_double_values
import Theorems.Thm_Couret_Strobo2Tors_rectangle_filter_first
import Theorems.Thm_Couret_Strobo2Tors_rectangle_filter_second
import Definitions.Def_Couret_RectangleFibres_2930a0e95467

/-!
STROBO: structural alternative for equality of two four-point rectangles.

Assuming each rectangle occupies two distinct fibres of the doubling map,
the pairs must match in their given order, or match after a swap.
This is a local theorem, not yet the convolution-square classification.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem p2m_local_rectangle_matching (x y u a b v : G)
    (hu : u + u = 0) (hv : v + v = 0)
    (hxy : doubleValue x ≠ doubleValue y)
    (hab : doubleValue a ≠ doubleValue b)
    (heq : rectangleSet x y u = rectangleSet a b v) :
    (pairSet x u = pairSet a v ∧ pairSet y u = pairSet b v) ∨
    (pairSet x u = pairSet b v ∧ pairSet y u = pairSet a v) := by
  have hdouble := rectangle_equal_double_values x y u a b v hu hv heq
  have hx : doubleValue x = doubleValue a ∨
      doubleValue x = doubleValue b := by
    have hmem : doubleValue x ∈
        ({doubleValue x, doubleValue y} : Finset G) := by simp
    rw [hdouble] at hmem
    simpa using hmem
  have hy : doubleValue y = doubleValue a ∨
      doubleValue y = doubleValue b := by
    have hmem : doubleValue y ∈
        ({doubleValue x, doubleValue y} : Finset G) := by simp
    rw [hdouble] at hmem
    simpa using hmem
  rcases hx with hxa | hxb
  · rcases hy with hya | hyb
    · exact False.elim (hxy (hxa.trans hya.symm))
    · left
      constructor
      · calc
          pairSet x u =
              (rectangleSet x y u).filter
                (fun z => doubleValue z = doubleValue x) :=
              (rectangle_filter_first x y u hu hxy).symm
          _ = (rectangleSet a b v).filter
                (fun z => doubleValue z = doubleValue a) := by rw [heq, hxa]
          _ = pairSet a v := rectangle_filter_first a b v hv hab
      · calc
          pairSet y u =
              (rectangleSet x y u).filter
                (fun z => doubleValue z = doubleValue y) :=
              (rectangle_filter_second x y u hu hxy).symm
          _ = (rectangleSet a b v).filter
                (fun z => doubleValue z = doubleValue b) := by rw [heq, hyb]
          _ = pairSet b v := rectangle_filter_second a b v hv hab
  · rcases hy with hya | hyb
    · right
      constructor
      · calc
          pairSet x u =
              (rectangleSet x y u).filter
                (fun z => doubleValue z = doubleValue x) :=
              (rectangle_filter_first x y u hu hxy).symm
          _ = (rectangleSet a b v).filter
                (fun z => doubleValue z = doubleValue b) := by rw [heq, hxb]
          _ = pairSet b v := rectangle_filter_second a b v hv hab
      · calc
          pairSet y u =
              (rectangleSet x y u).filter
                (fun z => doubleValue z = doubleValue y) :=
              (rectangle_filter_second x y u hu hxy).symm
          _ = (rectangleSet a b v).filter
                (fun z => doubleValue z = doubleValue a) := by rw [heq, hya]
          _ = pairSet a v := rectangle_filter_first a b v hv hab
    · exact False.elim (hxy (hxb.trans hyb.symm))

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
      @Ne.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst x)
          (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst y) →
        @Ne.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst a)
            (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst b) →
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.Strobo2Tors.rectangleSet.{p2m_u_0} G inst inst_2 x y u)
              (@Couret.Strobo2Tors.rectangleSet.{p2m_u_0} G inst inst_2 a b v) →
            Or
              (And
                (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 x u)
                  (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 a v))
                (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 y u)
                  (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 b v)))
              (And
                (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 x u)
                  (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 b v))
                (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 y u)
                  (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 a v))) := @_root_.Couret.Strobo2Tors.p2m_local_rectangle_matching

