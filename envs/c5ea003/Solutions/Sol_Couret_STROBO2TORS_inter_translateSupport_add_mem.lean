-- Prove2me | solution 1 for Couret.STROBO2TORS.inter_translateSupport_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:06.407809+00:00
-- url     : https://prove2.me/submissions/b674970c-1a55-48b0-b7d3-e87083fcc84a

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Ordinary partners and the intersection of distinct three-element supports.

The intersection of a support with its translate by a two-torsion element
is stable under that translation. A nonzero translation therefore cannot
leave exactly one point in the intersection. For distinct three-element
supports, the intersection has cardinality zero or two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translation by a two-torsion element preserves the intersection with
the translated support. -/
theorem p2m_local_inter_translateSupport_add_mem
    (S : Finset G) (u : G) (hu : u + u = 0) (x : G)
    (hx : x ∈ S ∩ translateSupport S u) :
    x + u ∈ S ∩ translateSupport S u := by
  obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
  apply Finset.mem_inter.mpr
  constructor
  · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxT
    have hxu : x + u = y := by
      rw [← hyx, add_assoc, hu, add_zero]
    rw [hxu]
    exact hy
  · exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩




end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (S : Finset.{p2m_u_0} G)
  (u : G),
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
    ∀ (x : G),
      @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
          (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
            (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
          x →
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
          (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S
            (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x u) := @_root_.Couret.STROBO2TORS.p2m_local_inter_translateSupport_add_mem

