-- Prove2me | solution 1 for Erdos390.Full.PaperScaleMarkedCell.headDivisorMain_sum_sub_common_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:30:55.22456+00:00
-- url     : https://prove2.me/submissions/a787a1db-2fa9-4cc6-8ca3-81fbd6a364e8

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_endpointMain_common_paper_bound

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/















/-! ## The common paper-scale main term -/































/-- Uniformly replacing every head-divisor endpoint by the common paper
translate costs only `O(n/(d log n))`; the right-hand coefficient is a
fixed finite sum depending on the head pattern and physical endpoints. -/
theorem headDivisorMain_sum_sub_common_le
    (P : Pattern) {A B : ℝ} {n d : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hn : 1 < n) (hd : 0 < d)
    (hd4 : d ≤ yNat n ^ 4) (hy2 : 2 ≤ y n)
    (hlogLower : (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ))
    (hmarginA : ∀ a ∈ P.modulus.divisors,
      4 ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      L n ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ))
    (hmarginB : ∀ a ∈ P.modulus.divisors,
      4 ≤ B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      L n ≤ B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ))
    (hlogA : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ))
    (hlogB : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ)) :
    |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a) -
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) *
            ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))| ≤
      (endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
        (n : ℝ) / ((d : ℝ) * L n) := by
  have hL : 0 < L n := L_pos hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a ∈ P.modulus.divisors,
        (headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a -
          (ArithmeticFunction.moebius a : ℝ) *
            ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)))| ≤
      ∑ a ∈ P.modulus.divisors,
        |headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a -
          (ArithmeticFunction.moebius a : ℝ) *
            ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (endpointCoefficient B (P.factor * a) *
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n +
            endpointCoefficient A (P.factor * a) *
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n) := by
      apply Finset.sum_le_sum
      intro a ha
      have hEndB := endpointMain_common_paper_bound B n
        (P.factor * a) d hB hn
        (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
          (Nat.pos_of_mem_divisors ha)) hd hd4 hy2 hlogLower
        (hmarginB a ha).1 (hmarginB a ha).2 (hlogB a ha)
      have hEndA := endpointMain_common_paper_bound A n
        (P.factor * a) d hA hn
        (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
          (Nat.pos_of_mem_divisors ha)) hd hd4 hy2 hlogLower
        (hmarginA a ha).1 (hmarginA a ha).2 (hlogA a ha)
      rw [show
        headDivisorMain P (physicalBound A n) (physicalBound B n)
              (yNat n) d a -
            (ArithmeticFunction.moebius a : ℝ) *
              ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                  rho (paperDivisorCoordinate n d) -
                (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                  rho (paperDivisorCoordinate n d)) =
          (ArithmeticFunction.moebius a : ℝ) *
            ((endpointMain (physicalBound B n / (P.factor * a * d))
                (yNat n) -
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)) -
             (endpointMain (physicalBound A n / (P.factor * a * d))
                (yNat n) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))) by
        unfold headDivisorMain
        ring]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hEndB' :
          |endpointMain (physicalBound B n / (P.factor * a * d)) (yNat n) -
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)| ≤
            endpointCoefficient B (P.factor * a) *
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n := by
        simpa only [endpointCoefficient] using hEndB
      have hEndA' :
          |endpointMain (physicalBound A n / (P.factor * a * d)) (yNat n) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)| ≤
            endpointCoefficient A (P.factor * a) *
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n := by
        simpa only [endpointCoefficient] using hEndA
      calc
        |_ - _| ≤ |endpointMain
              (physicalBound B n / (P.factor * a * d)) (yNat n) -
            (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
              rho (paperDivisorCoordinate n d)| +
          |endpointMain (physicalBound A n / (P.factor * a * d)) (yNat n) -
            (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
              rho (paperDivisorCoordinate n d)| := by
          rw [sub_eq_add_neg]
          simpa only [abs_neg] using abs_add_le
            (endpointMain (physicalBound B n / (P.factor * a * d)) (yNat n) -
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))
            (-(endpointMain (physicalBound A n / (P.factor * a * d)) (yNat n) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)))
        _ ≤ _ := add_le_add hEndB' hEndA'
    _ = (endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
        (n : ℝ) / ((d : ℝ) * L n) := by
      unfold endpointFamilyCoefficient
      have hdist (f : ℕ → ℝ) :
          (∑ a ∈ P.modulus.divisors, f a) * (n : ℝ) /
              ((d : ℝ) * L n) =
            ∑ a ∈ P.modulus.divisors,
              f a * (n : ℝ) / ((d : ℝ) * L n) := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [add_mul, add_div, hdist, hdist, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
      have haR : (0 : ℝ) < (a : ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors ha
      norm_num only [Nat.cast_mul]
      field_simp [hfactor.ne', haR.ne', hdR.ne', hL.ne']







/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

theorem solution :
∀ (P : Erdos390.Full.HeadPattern.Pattern) {A B : Real} {n d : Nat},
  LT.lt.{0} (0 : Real) A →
    LT.lt.{0} (0 : Real) B →
      LT.lt.{0} (1 : Nat) n →
        LT.lt.{0} (0 : Nat) d →
          LE.le.{0} d (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
            LE.le.{0} (2 : Real) (Erdos390.Full.ArithmeticModel.y n) →
              LE.le.{0} (HMul.hMul.{0, 0, 0} (1 / 5 : Real) (Erdos390.Full.Scale.L n))
                  (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
                (∀ (a : Nat),
                    Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                      And
                        (LE.le.{0} (4 : Real)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} A ↑n)
                            ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                d)))
                        (LE.le.{0} (Erdos390.Full.Scale.L n)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} A ↑n)
                            ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                d)))) →
                  (∀ (a : Nat),
                      Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                        And
                          (LE.le.{0} (4 : Real)
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑n)
                              ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                  d)))
                          (LE.le.{0} (Erdos390.Full.Scale.L n)
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑n)
                              ↑(HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a)
                                  d)))) →
                    (∀ (a : Nat),
                        Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                          LE.le.{0}
                            (Real.log
                              ↑(HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d)))
                            (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))) →
                      (∀ (a : Nat),
                          Membership.mem.{0, 0} (Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P)) a →
                            LE.le.{0}
                              (Real.log
                                ↑(HDiv.hDiv.{0, 0, 0} (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                    (HMul.hMul.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d)))
                              (HMul.hMul.{0, 0, 0} (5 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))) →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (∑ a ∈ Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P),
                                Erdos390.Full.StructuredCellAsymptotic.headDivisorMain P
                                  (Erdos390.Full.ArithmeticModel.physicalBound A n)
                                  (Erdos390.Full.ArithmeticModel.physicalBound B n)
                                  (Erdos390.Full.ArithmeticModel.yNat n) d a)
                              (∑ a ∈ Nat.divisors (Erdos390.Full.HeadPattern.Pattern.modulus P),
                                HMul.hMul.{0, 0, 0} (↑(ArithmeticFunction.moebius a))
                                  (HSub.hSub.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑n)
                                        ↑(HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d))
                                      (Erdos390.Full.DickmanBasic.rho
                                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisorCoordinate n d)))
                                    (HMul.hMul.{0, 0, 0}
                                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} A ↑n)
                                        ↑(HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (Erdos390.Full.HeadPattern.Pattern.factor P) a) d))
                                      (Erdos390.Full.DickmanBasic.rho
                                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisorCoordinate n d)))))))
                          (HDiv.hDiv.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PaperScaleMarkedCell.endpointFamilyCoefficient P B)
                                (Erdos390.Full.PaperScaleMarkedCell.endpointFamilyCoefficient P A))
                              ↑n)
                            (HMul.hMul.{0, 0, 0} (↑d) (Erdos390.Full.Scale.L n))) := by
  exact @Erdos390.Full.PaperScaleMarkedCell.headDivisorMain_sum_sub_common_le
