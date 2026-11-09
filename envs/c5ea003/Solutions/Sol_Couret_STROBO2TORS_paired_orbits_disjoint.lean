-- Prove2me | solution 1 for Couret.STROBO2TORS.paired_orbits_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:11.356026+00:00
-- url     : https://prove2.me/submissions/3afa6a3a-f7c3-4476-8fb1-69654f132f9c

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbits_disjoint
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]





























theorem p2m_local_paired_orbits_disjoint (a b d : G)
    (hd : d + d = 0) (hab : a + a ≠ b + b) :
    Disjoint (torsionOrbit ({a, b, b + d} : Finset G))
      (torsionOrbit ({a, b + b - a, (b + b - a) + d} : Finset G)) := by
  apply torsionOrbits_disjoint
  rintro ⟨u, hu, h⟩
  exact paired_reflection_not_two_torsion_translate a b d u hd hu hab h.symm




















/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a b d : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        d d)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Ne.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          a a)
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          b b) →
      @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.partialOrder.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.instOrderBot.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) b
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  b d)))))
        (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
            (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHSub.{p2m_u_0} G
                  (@SubNegMonoid.toSub.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  b b)
                a)
              (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHSub.{p2m_u_0} G
                      (@SubNegMonoid.toSub.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      b b)
                    a)
                  d))))) := @_root_.Couret.STROBO2TORS.p2m_local_paired_orbits_disjoint

