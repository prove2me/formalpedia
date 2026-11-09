-- Prove2me | solution 1 for Couret.InterIA.IntersectionThree.stable_common_part_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:32.100231+00:00
-- url     : https://prove2.me/submissions/1b0947be-52ef-4067-99a6-7c798d7fdd39

import Definitions.Def_Couret_SingleSwap_148f04e2e72b
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_IntersectionThree_e6b918e458b3

set_option autoImplicit false
namespace Couret.InterIA.IntersectionThree
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







/-- The common support's invariance is also sufficient, by the received translation law. -/
theorem p2m_local_stable_common_part_sufficient (C : Finset G) (a h : G) (hh2 : h+h=0)
    (hstable : ∀ z ∈ C, z+h ∈ C) :
    ∀ z, orderedSquare (insert a C) z = orderedSquare (insert (a+h) C) z := by
  have hC : C.image (fun x => x+h)=C := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact hstable x hx
    · intro hz
      refine Finset.mem_image.mpr ⟨z+h,hstable z hz,?_⟩
      rw [add_assoc,hh2,add_zero]
  have ht : (insert a C).image (fun x => x+h) = insert (a+h) C := by
    rw [Finset.image_insert,hC]
  intro z
  have he := Couret.InterIA.Translation.two_torsion_translation_preserves_square
    (insert a C) h hh2 z
  rw [ht] at he
  exact he.symm

end Couret.InterIA.IntersectionThree

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (C : Finset.{p2m_u_0} G)
  (a h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    (∀ (z : G),
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) C z →
          @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) C
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              z h)) →
      ∀ (z : G),
        @Eq.{1} Nat
          (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a C) z)
          (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a h)
              C)
            z) := @_root_.Couret.InterIA.IntersectionThree.p2m_local_stable_common_part_sufficient

