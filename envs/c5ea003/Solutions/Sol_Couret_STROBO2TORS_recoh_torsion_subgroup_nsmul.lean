-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_torsion_subgroup_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:33.785944+00:00
-- url     : https://prove2.me/submissions/2a952ea6-2605-4474-b8cd-8739fbdf4f46

import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality

set_option autoImplicit false

/-!
Primary complex character banks for finite abelian groups.

The construction takes coordinates on the subgroup killed by a prime p,
extends their standard complex characters to G, then raises each extension
to the factor of |G| coprime to p.  This gives p-primary characters without
assuming that G itself has exponent p.  All existence statements below are
proved from group structure and cardinality; separation is a conclusion.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]





/-- The subgroup is itself killed by `p`. -/
theorem p2m_local_recoh_torsion_subgroup_nsmul (p : ℕ)
    (x : recohTorsionSubgroup (G := G) p) : p • x = 0 :=
  Subtype.ext x.property



variable [Fintype G]

















end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] (p : Nat)
  (x :
    @Subtype.{p2m_u_0 + 1} G fun x =>
      @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x),
  @Eq.{p2m_u_0 + 1}
    (@Subtype.{p2m_u_0 + 1} G fun x =>
      @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x)
    (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x)
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x)
      (@instHSMul.{0, p2m_u_0} Nat
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x)
        (@AddSubgroup.nsmul.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p)))
      p x)
    (@OfNat.ofNat.{p2m_u_0}
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x)
      (nat_lit 0)
      (@Zero.toOfNat0.{p2m_u_0}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p) x)
        (@AddSubgroup.zero.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst p)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_torsion_subgroup_nsmul

