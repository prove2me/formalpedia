-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_first_trace_difference_at_quotient_third
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:18.989457+00:00
-- url     : https://prove2.me/submissions/1ec102e7-1490-4e56-af2d-3dff47648c3a

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_trace_difference
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_exists_canonical_odd_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_trace_eq_before_third
import Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — spectral necessity and classification for the directed triple pair.

The cyclic odd witness, exact odd-trace criterion, canonical third-period
return, and sufficient direction are reused without changing their modules.
The generic characteristic-polynomial-to-power-trace theorem discharges the
explicit bridge left open by the earlier conditional assembly.

Every adjacency matrix here is the existing directed Finset adjacency matrix.
No loop exclusion, undirected reinterpretation, or scientific novelty claim is
introduced. The coefficient-level Newton identities remain separate results.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- In the fully generated odd-quotient branch, the first power at which
the traces differ is exactly one third of the quotient cardinality.
The witness is positive and odd; every smaller power has equal traces.
This diagnostic uses only the previously established group and trace lemmas,
independently of the characteristic-polynomial bridge. -/
theorem p2m_local_abelianThree_first_trace_difference_at_quotient_third
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    let k := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
    0 < k ∧ Odd k ∧
      (∀ j : ℕ, j < k →
        Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ j) =
          Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ j)) ∧
      Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ k) ≠
        Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ k) := by
  obtain ⟨ell, hell, hellodd, hsize, _⟩ :=
    abelianThree_exists_canonical_odd_return a d h hpair hodd horder
  have hk : Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3 = ell := by omega
  dsimp only
  rw [hk]
  have hord : addOrderOf (a : G ⧸ AddSubgroup.zmultiples h) = 3 * ell := by
    rw [quotient_alpha_order_of_pair_generation a h hpair, hsize]
  refine ⟨hell, hellodd, ?_, ?_⟩
  · intro j hj
    exact abelianThree_trace_eq_before_third a d h ell j
      hhalf hne horder hord hj
  · exact abelianThree_canonical_odd_trace_difference a d h ell
      hhalf hne hpair hodd hell hsize horder







end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d h : G),
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
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{1} Nat
          (@addOrderOf.{p2m_u_0}
            (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
            (@SubNegMonoid.toAddMonoid.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
              (@AddGroup.toSubNegMonoid.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                  (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
            (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Eq.{p2m_u_0 + 1} (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@AddSubgroup.closure.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@Insert.insert.{p2m_u_0, p2m_u_0} G (Set.{p2m_u_0} G) (@Set.instInsert.{p2m_u_0} G) a
                (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Set.{p2m_u_0} G) (@Set.instSingletonSet.{p2m_u_0} G) h)))
            (@Top.top.{p2m_u_0} (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@AddSubgroup.instTop.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))) →
          @Odd.{0} Nat Nat.instSemiring
              (Nat.card.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))) →
            have k :=
              @HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Nat.card.{p2m_u_0}
                  (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)));
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (And (@Odd.{0} Nat Nat.instSemiring k)
                (And
                  (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j k →
                      @Eq.{1} Rat
                        (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                            (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                            (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                              (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                  (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                            (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                              (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                            j))
                        (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                            (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                            (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                              (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                                  (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                            (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                              (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                            j)))
                  (@Ne.{1} Rat
                    (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                      (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                        (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                          (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                            (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                              (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                        (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                          (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                        k))
                    (@Matrix.trace.{p2m_u_0, 0} G Rat inst_2 Rat.addCommMonoid
                      (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                        (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                        (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
                          (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                            (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                              (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
                        (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                          (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                        k))))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_first_trace_difference_at_quotient_third

