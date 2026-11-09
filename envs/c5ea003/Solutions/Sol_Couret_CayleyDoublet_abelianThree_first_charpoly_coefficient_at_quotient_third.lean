-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_first_charpoly_coefficient_at_quotient_third
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:42.073359+00:00
-- url     : https://prove2.me/submissions/22be1966-d821-4ddf-b503-e80d1d98fbbd

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_trace_difference_at_quotient_third
import Theorems.Thm_Couret_CayleyNewton_newton_coefficient_prefix_eq
import Theorems.Thm_Couret_CayleyNewton_newton_first_coefficient_ne_of_trace_prefix
import Theorems.Thm_Couret_CayleyNewton_satisfiesMatrixNewton
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20: the first differing characteristic-polynomial coefficient.

The original spectral equivalence and first-trace certificates are imported
unchanged. We reuse the previously proved finite Newton prefix identities,
the generic single-matrix Newton theorem, and the canonical odd quotient
return. All statements refer to the actual rational directed adjacency
matrices (including their loops).

The numerical absolute-gap formula remains a documented mathematical
corollary, not a claim of formalization in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- In the generated odd-quotient case, the coefficient of X^(|G|-k)
with k=|G/<h>|/3 is the first *non-leading* characteristic-polynomial
coefficient that differs. The leading coefficient (index zero) is 1
for both monic characteristic polynomials.
No extra global-generation premise is used. -/
theorem p2m_local_abelianThree_first_charpoly_coefficient_at_quotient_third
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    (∀ j : ℕ, 0 < j →
      j < Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3 →
      reverseCharpolyCoeff (abelianCayleyMatrix (AbelianSource a d h)) j =
        reverseCharpolyCoeff (abelianCayleyMatrix (AbelianTarget a d h)) j) ∧
    reverseCharpolyCoeff (abelianCayleyMatrix (AbelianSource a d h))
      (Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3) ≠
    reverseCharpolyCoeff (abelianCayleyMatrix (AbelianTarget a d h))
      (Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3) := by
  let k : ℕ := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
  let A : Matrix G G ℚ := abelianCayleyMatrix (AbelianSource a d h)
  let B : Matrix G G ℚ := abelianCayleyMatrix (AbelianTarget a d h)
  have hfirst : 0 < k ∧ Odd k ∧
      (∀ j : ℕ, j < k → Matrix.trace (A ^ j) = Matrix.trace (B ^ j)) ∧
      Matrix.trace (A ^ k) ≠ Matrix.trace (B ^ k) :=
    abelianThree_first_trace_difference_at_quotient_third
      a d h hhalf hne horder hpair hodd
  obtain ⟨hk, _, hprev, hdiff⟩ := hfirst
  have hprevPos : ∀ j : ℕ, 0 < j → j < k →
      Matrix.trace (A ^ j) = Matrix.trace (B ^ j) := by
    intro j _ hj
    exact hprev j hj
  have hS : SatisfiesMatrixNewton A := satisfiesMatrixNewton A
  have hT : SatisfiesMatrixNewton B := satisfiesMatrixNewton B
  have hprefix : ∀ j : ℕ, 0 < j → j < k →
      reverseCharpolyCoeff A j = reverseCharpolyCoeff B j :=
    newton_coefficient_prefix_eq
      (reverseCharpolyCoeff A) (reverseCharpolyCoeff B)
      (fun j => Matrix.trace (A ^ j)) (fun j => Matrix.trace (B ^ j)) k
      (fun j hj _ => hS j hj) (fun j hj _ => hT j hj) hprevPos
  have hgap : reverseCharpolyCoeff A k ≠ reverseCharpolyCoeff B k :=
    newton_first_coefficient_ne_of_trace_prefix
      (reverseCharpolyCoeff A) (reverseCharpolyCoeff B)
      (fun j => Matrix.trace (A ^ j)) (fun j => Matrix.trace (B ^ j))
      k hk (fun j hj _ => hS j hj) (fun j hj _ => hT j hj)
      hprevPos hdiff
  exact ⟨hprefix, hgap⟩











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
            And
              (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
                  @LT.lt.{0} Nat instLTNat j
                      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                        (Nat.card.{p2m_u_0}
                          (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                            (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                              (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                            (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                    @Eq.{1} Rat
                      (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                        (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                          (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                        j)
                      (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                        (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                          (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                        j))
              (@Ne.{1} Rat
                (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                  (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                    (Nat.card.{p2m_u_0}
                      (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                  (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                    (Nat.card.{p2m_u_0}
                      (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G
                          (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_first_charpoly_coefficient_at_quotient_third

