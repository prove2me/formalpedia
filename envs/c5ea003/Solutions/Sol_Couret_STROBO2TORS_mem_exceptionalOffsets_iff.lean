-- Prove2me | solution 1 for Couret.STROBO2TORS.mem_exceptionalOffsets_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:19.108249+00:00
-- url     : https://prove2.me/submissions/16818d8a-097e-45fc-8fcc-fdbd7b4ae56a

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_triple_condition_iff
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalOffsets
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









theorem triple_sum_two_torsion_shift (w d : G) (hd : d + d = 0) :
    ((w + d) + (w + d)) + (w + d) = ((w + w) + w) + d := by
  calc
    ((w + d) + (w + d)) + (w + d) =
        ((w + w) + w) + ((d + d) + d) := by abel
    _ = ((w + w) + w) + d := by rw [hd]; simp





theorem nonzero_three_torsion_double_ne_zero (w : G)
    (hw : (w + w) + w = 0) (hw0 : w ≠ 0) : w + w ≠ 0 := by
  intro h2
  have hz : w = 0 := by
    calc
      w = ((w + w) + w) - (w + w) := by abel
      _ = 0 := by rw [hw, h2]; simp
  exact hw0 hz

/-- Exact offset predicate: genuine doubled difference and exceptional triple sum. -/
theorem p2m_local_mem_exceptionalOffsets_iff (v d : G) (hd : d + d = 0) :
    v ∈ exceptionalOffsets d ↔
      (v + v ≠ 0 ∧ (((v + v) + v = 0) ∨ ((v + v) + v = d))) := by
  constructor
  · intro hv
    obtain ⟨w, hw3, hw0, hvw⟩ := (mem_exceptionalOffsets v d).mp hv
    rcases hvw with h | h
    · subst v
      exact ⟨nonzero_three_torsion_double_ne_zero w hw3 hw0, Or.inl hw3⟩
    · subst v
      constructor
      · rw [pair_sum_translate w w d hd]
        exact nonzero_three_torsion_double_ne_zero w hw3 hw0
      · right
        rw [triple_sum_two_torsion_shift w d hd, hw3]
        simp
  · rintro ⟨hv2, h3⟩
    obtain ⟨w, hw3, hwv⟩ := (exceptional_triple_condition_iff v d hd).mp h3
    have hw2 : w + w ≠ 0 := by
      rcases hwv with h | h
      · subst v; exact hv2
      · intro hz
        apply hv2
        rw [h, pair_sum_translate w w d hd]
        exact hz
    have hw0 : w ≠ 0 := by
      intro hz; apply hw2; simp [hz]
    exact (mem_exceptionalOffsets v d).mpr ⟨w, hw3, hw0, hwv⟩





end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (v d : G),
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
    Iff
      (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
        (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
        (@Couret.STROBO2TORS.exceptionalOffsets.{p2m_u_0} G inst inst_1 inst_2 d) v)
      (And
        (@Ne.{p2m_u_0 + 1} G
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
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (Or
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
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                v v)
              v)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
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
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                v v)
              v)
            d))) := @_root_.Couret.STROBO2TORS.p2m_local_mem_exceptionalOffsets_iff

