-- Prove2me | solution 1 for Couret.STROBO2TORS.mem_exceptionalOffsets
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:50.851919+00:00
-- url     : https://prove2.me/submissions/9bd1e7dc-f5a7-4885-95dc-b4b2245be44d

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





theorem p2m_local_mem_exceptionalOffsets (v d : G) :
    v ∈ exceptionalOffsets d ↔
      ∃ w : G, (w + w) + w = 0 ∧ w ≠ 0 ∧
        (v = w ∨ v = w + d) := by
  rw [exceptionalOffsets, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨hw, hw0⟩ := (mem_nonzeroThreeTorsion v).mp h
      exact ⟨v, hw, hw0, Or.inl rfl⟩
    · obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
      obtain ⟨hw3, hw0⟩ := (mem_nonzeroThreeTorsion w).mp hw
      exact ⟨w, hw3, hw0, Or.inr hwv.symm⟩
  · rintro ⟨w, hw3, hw0, hv | hv⟩
    · apply Or.inl
      rw [hv]
      exact (mem_nonzeroThreeTorsion w).mpr ⟨hw3, hw0⟩
    · apply Or.inr
      exact Finset.mem_image.mpr
        ⟨w, (mem_nonzeroThreeTorsion w).mpr ⟨hw3, hw0⟩, hv.symm⟩









end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (v d : G),
  Iff
    (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
      (@Couret.STROBO2TORS.exceptionalOffsets.{p2m_u_0} G inst inst_1 inst_2 d) v)
    (@Exists.{p2m_u_0 + 1} G fun w =>
      And
        (@Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              w w)
            w)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (And
          (@Ne.{p2m_u_0 + 1} G w
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
          (Or (@Eq.{p2m_u_0 + 1} G v w)
            (@Eq.{p2m_u_0 + 1} G v
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                w d))))) := @_root_.Couret.STROBO2TORS.p2m_local_mem_exceptionalOffsets

