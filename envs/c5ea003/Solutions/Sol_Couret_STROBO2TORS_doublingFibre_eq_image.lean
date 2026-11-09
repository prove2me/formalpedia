-- Prove2me | solution 1 for Couret.STROBO2TORS.doublingFibre_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:11.510942+00:00
-- url     : https://prove2.me/submissions/8803115e-e559-4708-9b03-cccba67368ef

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]







































theorem p2m_local_doublingFibre_eq_image (a : G) :
    (Finset.univ : Finset G).filter (fun x => x + x = a + a) =
      (twoTorsion : Finset G).image (fun u => a + u) := by
  ext x
  constructor
  · intro h
    have hx := (Finset.mem_filter.mp h).2
    have hu : (x - a) + (x - a) = 0 :=
      (double_eq_iff_two_torsion a x).mp hx.symm
    exact Finset.mem_image.mpr ⟨x - a, (mem_twoTorsion _).mpr hu, by abel⟩
  · intro h
    obtain ⟨u, hu, hx⟩ := Finset.mem_image.mp h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hx]
    exact pair_sum_translate a a u ((mem_twoTorsion u).mp hu)

















































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a : G),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
    (@Finset.filter.{p2m_u_0} G
      (fun x =>
        @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x x)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a a))
      (fun a_1 =>
        inst_1
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a_1 a_1)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a a))
      (@Finset.univ.{p2m_u_0} G inst_2))
    (@Finset.image.{p2m_u_0, p2m_u_0} G G inst_1
      (fun u =>
        @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          a u)
      (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_doublingFibre_eq_image

