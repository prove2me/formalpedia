-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalOffsets_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:39.620375+00:00
-- url     : https://prove2.me/submissions/accf9151-fda5-47a3-8be0-5d6f0deb8b67

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/







theorem mem_nonzeroThreeTorsion (w : G) :
    w ∈ (nonzeroThreeTorsion : Finset G) ↔
      (w + w) + w = 0 ∧ w ≠ 0 := by
  simp [nonzeroThreeTorsion, offsetThreeTorsion, and_comm]

theorem triple_sum_two_torsion_shift (w d : G) (hd : d + d = 0) :
    ((w + d) + (w + d)) + (w + d) = ((w + w) + w) + d := by
  calc
    ((w + d) + (w + d)) + (w + d) =
        ((w + w) + w) + ((d + d) + d) := by abel
    _ = ((w + w) + w) + d := by rw [hd]; simp









theorem p2m_local_exceptionalOffsets_disjoint (d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) :
    Disjoint (nonzeroThreeTorsion : Finset G)
      ((nonzeroThreeTorsion : Finset G).image (fun w => w + d)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hshift
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hshift
  have hv3 := ((mem_nonzeroThreeTorsion v).mp hv).1
  have hw3 := ((mem_nonzeroThreeTorsion w).mp hw).1
  have hdz : d = 0 := by
    calc
      d = ((w + w) + w) + d := by simp [hw3]
      _ = ((w + d) + (w + d)) + (w + d) :=
        (triple_sum_two_torsion_shift w d hd).symm
      _ = ((v + v) + v) := by rw [hwv]
      _ = 0 := hv3
  exact hd0 hdz



end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (d : G),
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
    @Ne.{p2m_u_0 + 1} G d
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.partialOrder.{p2m_u_0} G) (@Finset.instOrderBot.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nonzeroThreeTorsion.{p2m_u_0} G inst inst_1 inst_2)
        (@Finset.image.{p2m_u_0, p2m_u_0} G G inst_1
          (fun w =>
            @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              w d)
          (@Couret.STROBO2TORS.nonzeroThreeTorsion.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalOffsets_disjoint

