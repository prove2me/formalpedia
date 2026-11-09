-- Prove2me | solution 1 for Couret.Strobo2Tors.tripleDelta_iff_crossed_exists
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:02.403365+00:00
-- url     : https://prove2.me/submissions/b18cb84c-7f93-4dce-b349-a043ff1bc7d0

import Definitions.Def_Couret_CrossedOrderThree_8ba7af1c9194
import Mathlib
import Theorems.Thm_Couret_Strobo2Tors_crossed_forces_tripleDelta
import Theorems.Thm_Couret_Strobo2Tors_pair_coset_eq_iff
import Definitions.Def_Couret_RectangleFibres_2930a0e95467

/-!
STROBO-2TORS: normalized type-II crossed matching.

This theorem isolates the 3-torsion obstruction in the branch where the
singleton representatives have been aligned (d = b).
It proves equivalence at the level of equal two-point cosets, not yet
equivalence with SameSquare of arbitrary triple supports.
-/

namespace Couret.Strobo2Tors

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]





/-- The 3-torsion obstruction is also sufficient for a normalized
crossed matching: choose the opposite double-fibre representative
`c = 2a-b`. -/
theorem p2m_local_tripleDelta_iff_crossed_exists (a b u : G) (hu : u + u = 0) :
    (∃ c : G,
      pairSet (c + c) u = pairSet (a + b) u ∧
      pairSet (c + b) u = pairSet (a + a) u) ↔
    tripleDelta a b = 0 ∨ tripleDelta a b = u := by
  constructor
  · rintro ⟨c, hfirst, hsecond⟩
    exact crossed_forces_tripleDelta a b c u hu hfirst hsecond
  · intro hd
    refine ⟨a + a - b, ?_, ?_⟩
    · have hc :
          (a + a - b) + (a + a - b) =
            (a + b) - tripleDelta a b := by
        dsimp [tripleDelta]
        abel
      rcases hd with hd | hd
      · have he : (a + a - b) + (a + a - b) = a + b := by
          rw [hc, hd]
          simp
        rw [he]
      · have hneg : -u = u := by
          calc
            -u = -u + (u + u) := by rw [hu]; simp
            _ = u := by abel
        have he : (a + a - b) + (a + a - b) = (a + b) + u := by
          rw [hc, hd]
          rw [sub_eq_add_neg, hneg]
        rw [he]
        exact ((pair_coset_eq_iff (a + b) ((a + b) + u) u hu).mpr
          (Or.inr rfl)).symm
    · have he : (a + a - b) + b = a + a := by abel
      rw [he]

end Couret.Strobo2Tors

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [Fintype.{p2m_u_0} G] [inst_2 : DecidableEq.{p2m_u_0 + 1} G]
  (a b u : G),
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
    Iff
      (@Exists.{p2m_u_0 + 1} G fun c =>
        And
          (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                c c)
              u)
            (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a b)
              u))
          (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                c b)
              u)
            (@Couret.Strobo2Tors.pairSet.{p2m_u_0} G inst inst_2
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a a)
              u)))
      (Or
        (@Eq.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.tripleDelta.{p2m_u_0} G inst a b)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (@Eq.{p2m_u_0 + 1} G (@Couret.Strobo2Tors.tripleDelta.{p2m_u_0} G inst a b) u)) := @_root_.Couret.Strobo2Tors.p2m_local_tripleDelta_iff_crossed_exists

