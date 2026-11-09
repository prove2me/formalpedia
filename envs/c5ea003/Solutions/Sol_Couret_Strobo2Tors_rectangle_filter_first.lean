-- Prove2me | solution 1 for Couret.Strobo2Tors.rectangle_filter_first
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:30:36.588085+00:00
-- url     : https://prove2.me/submissions/efd38e1a-d781-4220-8251-8b3338665342

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

theorem doubleValue_of_mem_pairSet (x u z : G) (hu : u + u = 0)
    (hz : z ∈ pairSet x u) : doubleValue z = doubleValue x := by
  simp only [pairSet, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · rfl
  · exact doubleValue_add_torsion x u hu

theorem p2m_local_rectangle_filter_first (x y u : G)
    (hu : u + u = 0) (hxy : doubleValue x ≠ doubleValue y) :
    (rectangleSet x y u).filter (fun z => doubleValue z = doubleValue x) =
      pairSet x u := by
  ext z
  constructor
  · intro hz
    obtain ⟨hrect, hdouble⟩ := Finset.mem_filter.mp hz
    rcases Finset.mem_union.mp hrect with hl | hr
    · exact hl
    · have hother := doubleValue_of_mem_pairSet y u z hu hr
      exact False.elim (hxy (hdouble.symm.trans hother))
  · intro hz
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union.mpr (Or.inl hz), doubleValue_of_mem_pairSet x u z hu hz⟩







end Couret.Strobo2Tors

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [Fintype.{p2m_u_0} G] [inst_2 : DecidableEq.{p2m_u_0 + 1} G]
  (x y u : G),
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
    @Ne.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst x)
        (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst y) →
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
        (@Finset.filter.{p2m_u_0} G
          (fun z =>
            @Eq.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst z)
              (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst x))
          (fun a =>
            inst_2 (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst a)
              (@Couret.Strobo2Tors.doubleValue.{p2m_u_0} G inst x))
          (@Couret.Strobo2Tors.rectangleSet.{p2m_u_0} G inst inst_2 x y u))
        (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2 x u) := @_root_.Couret.Strobo2Tors.p2m_local_rectangle_filter_first

