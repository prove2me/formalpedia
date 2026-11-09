-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThree_first_charpoly_coefficient_abs_gap
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:05.009995+00:00
-- url     : https://prove2.me/submissions/90c9772a-2b6f-4928-9e46-34a2509370fc

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_card_eq_six_quotient_third
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_exists_canonical_odd_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_charpoly_coefficient_gap_at_quotient_third
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_trace_difference_at_quotient_third
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_gap_abs_of_ne
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










/-- Fully numerical first coefficient discrepancy in the odd quotient
branch: the magnitude is 6*3^((k-1)/2), k=card(G/<h>)/3. -/
theorem p2m_local_abelianThree_first_charpoly_coefficient_abs_gap
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    let k := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
    |reverseCharpolyCoeff (abelianCayleyMatrix (AbelianSource a d h)) k -
      reverseCharpolyCoeff (abelianCayleyMatrix (AbelianTarget a d h)) k| =
      6 * (3 : ℚ) ^ ((k - 1) / 2) := by
  let k : ℕ := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
  let A : Matrix G G ℚ := abelianCayleyMatrix (AbelianSource a d h)
  let B : Matrix G G ℚ := abelianCayleyMatrix (AbelianTarget a d h)
  have hfirst := abelianThree_first_trace_difference_at_quotient_third
    a d h hhalf hne horder hpair hodd
  dsimp only at hfirst
  obtain ⟨hk, hkodd, _, hdiff⟩ := hfirst
  obtain ⟨n, hn⟩ := hkodd
  have hncalc : (k - 1) / 2 = n := by omega
  have hsize : Nat.card (G ⧸ AddSubgroup.zmultiples h) = 3 * k := by
    obtain ⟨ell, _, _, hcard, _⟩ :=
      abelianThree_exists_canonical_odd_return a d h hpair hodd horder
    dsimp only [k]
    omega
  have hcNat : Fintype.card G = 6 * k :=
    abelianThree_card_eq_six_quotient_third h hhalf hne k hsize
  have hc : (Fintype.card G : ℚ) = 6 * (k : ℚ) := by
    exact_mod_cast hcNat
  have hk' : k = 2 * n + 1 := hn
  have htrace :
      |Matrix.trace (A ^ k) - Matrix.trace (B ^ k)| =
        (Fintype.card G : ℚ) * (3 : ℚ) ^ n := by
    have hdiffK : Matrix.trace (A ^ k) ≠ Matrix.trace (B ^ k) := by
      exact hdiff
    have hdiffN : Matrix.trace (A ^ (2 * n + 1)) ≠
        Matrix.trace (B ^ (2 * n + 1)) := by
      simpa only [hk'] using hdiffK
    rw [hk']
    exact abelianThree_odd_trace_gap_abs_of_ne a d h
      hhalf hne horder n hdiffN
  have hnewton :
      (k : ℚ) * (reverseCharpolyCoeff A k - reverseCharpolyCoeff B k) =
       -(Matrix.trace (A ^ k) - Matrix.trace (B ^ k)) :=
    abelianThree_first_charpoly_coefficient_gap_at_quotient_third
      a d h hhalf hne horder hpair hodd
  have habs := congrArg abs hnewton
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (k : ℚ)),
    abs_neg, htrace, hc] at habs
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hmul :
      (k : ℚ) * |reverseCharpolyCoeff A k - reverseCharpolyCoeff B k| =
        (k : ℚ) * (6 * (3 : ℚ) ^ n) := by
    calc
      _ = 6 * (k : ℚ) * (3 : ℚ) ^ n := habs
      _ = _ := by ring
  have hcoeff : |reverseCharpolyCoeff A k - reverseCharpolyCoeff B k| =
      6 * (3 : ℚ) ^ n :=
    (mul_left_cancel₀ hk0) hmul
  change |reverseCharpolyCoeff A k - reverseCharpolyCoeff B k| =
    6 * (3 : ℚ) ^ ((k - 1) / 2)
  simpa only [hncalc] using hcoeff


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
            @Eq.{1} Rat
              (@abs.{0} Rat Rat.instLattice Rat.addGroup
                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                  (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                    (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                      (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
                    k)
                  (@Couret.CayleyNewton.reverseCharpolyCoeff.{p2m_u_0} G inst_2 inst_1
                    (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                      (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
                    k)))
              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                (@OfNat.ofNat.{0} Rat (nat_lit 6) (@Rat.instOfNat (nat_lit 6)))
                (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                  (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
                  (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThree_first_charpoly_coefficient_abs_gap

