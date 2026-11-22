-- Prove2me | solution 1 for Erdos390.Full.TwoLocalRestorationBound.abs_pairRestoredNumerator_sub_expect_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:32:54.893787+00:00
-- url     : https://prove2.me/submissions/70ab53e9-5fb4-4cc6-931d-06357a8ae3f6

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.ArithmeticModel -/
section


/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel















































theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]























































end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.TwoLocalRestorationBound -/
section


/-!
# Quantitative error of the exact two-local restoration

This file bounds every nonconstant term in the exact `N_{r,s}` numerator
using the arbitrary-modulus reciprocal fallback.  The result retains the
paper's weighted coefficient tails in both local coordinates; in particular,
it does not replace them by the cardinality of the exponent cutoff.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalRestorationBound

open ArithmeticModel FiniteProbability LocalFugacity LocalFugacityBounds
open OmittedTiltPairChamber

noncomputable section

variable {Omega : Type*} [Fintype Omega]







private theorem Icc_zero_eq_insert (A : ℕ) :
    Finset.Icc 0 A = insert 0 (Finset.Icc 1 A) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private theorem sum_Icc_zero_eq (A : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 0 A, f a) =
      f 0 + ∑ a ∈ Finset.Icc 1 A, f a := by
  rw [Icc_zero_eq_insert]
  have hzero : 0 ∉ Finset.Icc 1 A := by simp
  rw [Finset.sum_insert hzero]

/-- Exact separation of the constant, one-local, and two-local pieces. -/
theorem pairRestoredNumerator_decomposition
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    (p q Ap Aq : ℕ) (etaP etaQ L : ℝ) (r s : ℕ) :
    pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s =
      nu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)) +
      (∑ a ∈ Finset.Icc 1 Ap,
        coefficient (Real.exp (etaP / L)) a *
          nu.expect (fun omega ↦
            divInd (pairPower p q (max r a) s) (value omega))) +
      (∑ b ∈ Finset.Icc 1 Aq,
        coefficient (Real.exp (etaQ / L)) b *
          nu.expect (fun omega ↦
            divInd (pairPower p q r (max s b)) (value omega))) +
      (∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
        coefficient (Real.exp (etaP / L)) a *
          coefficient (Real.exp (etaQ / L)) b *
            nu.expect (fun omega ↦
              divInd (pairPower p q (max r a) (max s b))
                (value omega))) := by
  unfold pairRestoredNumerator
  rw [sum_Icc_zero_eq]
  simp_rw [sum_Icc_zero_eq]
  simp only [coefficient_zero, max_eq_left (Nat.zero_le _), one_mul]
  rw [Finset.sum_add_distrib]
  ring_nf

private theorem abs_sum_mul_expect_le
    (nu : FiniteProbability Omega) (T : Finset ℕ)
    (c : ℕ → ℝ) (A : ℕ → Omega → ℝ)
    (hA : ∀ i ∈ T, ∀ omega, 0 ≤ A i omega) :
    |∑ i ∈ T, c i * nu.expect (A i)| ≤
      ∑ i ∈ T, |c i| * nu.expect (A i) := by
  calc
    |∑ i ∈ T, c i * nu.expect (A i)| ≤
        ∑ i ∈ T, |c i * nu.expect (A i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ T, |c i| * nu.expect (A i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (nu.expect_nonneg (A i) (hA i hi))]

/-- All restoration terms are controlled by the exact weighted coefficient
tails.  `G` is the reciprocal-event constant supplied by the arbitrary
modulus fallback. -/
theorem abs_pairRestoredNumerator_sub_expect_le
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q Ap Aq r s : ℕ} {etaP etaQ L G : ℝ}
    (hprob : ∀ u v : ℕ,
      nu.expect (fun omega ↦ divInd (pairPower p q u v) (value omega)) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v)) :
    |pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s -
        nu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega))| ≤
      pairRestorationError p q Ap Aq r s etaP etaQ L G := by
  let EP : ℕ → ℝ := fun a ↦ nu.expect (fun omega ↦
    divInd (pairPower p q (max r a) s) (value omega))
  let EQ : ℕ → ℝ := fun b ↦ nu.expect (fun omega ↦
    divInd (pairPower p q r (max s b)) (value omega))
  let EPQ : ℕ → ℕ → ℝ := fun a b ↦ nu.expect (fun omega ↦
    divInd (pairPower p q (max r a) (max s b)) (value omega))
  let cp : ℕ → ℝ := fun a ↦ coefficient (Real.exp (etaP / L)) a
  let cq : ℕ → ℝ := fun b ↦ coefficient (Real.exp (etaQ / L)) b
  let SP : ℝ := ∑ a ∈ Finset.Icc 1 Ap, cp a * EP a
  let SQ : ℝ := ∑ b ∈ Finset.Icc 1 Aq, cq b * EQ b
  let SPQ : ℝ := ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
    cp a * cq b * EPQ a b
  have hdecomp :
      pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s -
          nu.expect (fun omega ↦
            divInd (pairPower p q r s) (value omega)) = SP + SQ + SPQ := by
    rw [pairRestoredNumerator_decomposition]
    dsimp only [SP, SQ, SPQ, EP, EQ, EPQ, cp, cq]
    ring
  have hEP0 : ∀ a, 0 ≤ EP a := by
    intro a
    exact nu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hEQ0 : ∀ b, 0 ≤ EQ b := by
    intro b
    exact nu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hEPQ0 : ∀ a b, 0 ≤ EPQ a b := by
    intro a b
    exact nu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hSP : |SP| ≤
      G * coefficientTail p Ap r etaP L * (1 / (q : ℝ) ^ s) := by
    calc
      |SP| ≤ ∑ a ∈ Finset.Icc 1 Ap, |cp a| * EP a := by
        dsimp only [SP]
        exact abs_sum_mul_expect_le nu (Finset.Icc 1 Ap) cp
          (fun a omega ↦ divInd (pairPower p q (max r a) s) (value omega))
          (fun a ha omega ↦ divInd_nonneg _ _)
      _ ≤ ∑ a ∈ Finset.Icc 1 Ap,
          |cp a| * (G / ((p : ℝ) ^ max r a * (q : ℝ) ^ s)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hprob (max r a) s) (abs_nonneg _)
      _ = G * coefficientTail p Ap r etaP L * (1 / (q : ℝ) ^ s) := by
        unfold coefficientTail
        dsimp only [cp]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        norm_num only [Nat.cast_pow]
        ring
  have hSQ : |SQ| ≤
      G * (1 / (p : ℝ) ^ r) * coefficientTail q Aq s etaQ L := by
    calc
      |SQ| ≤ ∑ b ∈ Finset.Icc 1 Aq, |cq b| * EQ b := by
        dsimp only [SQ]
        exact abs_sum_mul_expect_le nu (Finset.Icc 1 Aq) cq
          (fun b omega ↦ divInd (pairPower p q r (max s b)) (value omega))
          (fun b hb omega ↦ divInd_nonneg _ _)
      _ ≤ ∑ b ∈ Finset.Icc 1 Aq,
          |cq b| * (G / ((p : ℝ) ^ r * (q : ℝ) ^ max s b)) := by
        apply Finset.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left (hprob r (max s b)) (abs_nonneg _)
      _ = G * (1 / (p : ℝ) ^ r) * coefficientTail q Aq s etaQ L := by
        unfold coefficientTail
        dsimp only [cq]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        norm_num only [Nat.cast_pow]
        ring
  have hSPQ : |SPQ| ≤
      G * coefficientTail p Ap r etaP L *
        coefficientTail q Aq s etaQ L := by
    calc
      |SPQ| ≤ ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
          |cp a * cq b * EPQ a b| := by
        dsimp only [SPQ]
        calc
          |∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
              cp a * cq b * EPQ a b| ≤
              ∑ a ∈ Finset.Icc 1 Ap,
                |∑ b ∈ Finset.Icc 1 Aq, cp a * cq b * EPQ a b| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
              |cp a * cq b * EPQ a b| := by
            apply Finset.sum_le_sum
            intro a ha
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
          |cp a| * |cq b| * EPQ a b := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [abs_mul, abs_mul, abs_of_nonneg (hEPQ0 a b)]
      _ ≤ ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
          |cp a| * |cq b| *
            (G / ((p : ℝ) ^ max r a * (q : ℝ) ^ max s b)) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left (hprob (max r a) (max s b))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = G * coefficientTail p Ap r etaP L *
          coefficientTail q Aq s etaQ L := by
        unfold coefficientTail
        dsimp only [cp, cq]
        calc
          (∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
              |coefficient (Real.exp (etaP / L)) a| *
                |coefficient (Real.exp (etaQ / L)) b| *
                (G / ((p : ℝ) ^ max r a * (q : ℝ) ^ max s b))) =
              ∑ a ∈ Finset.Icc 1 Ap,
                (G * (|coefficient (Real.exp (etaP / L)) a| /
                  (p : ℝ) ^ max r a)) *
                  (∑ b ∈ Finset.Icc 1 Aq,
                    |coefficient (Real.exp (etaQ / L)) b| /
                      (q : ℝ) ^ max s b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            ring
          _ = G *
              (∑ a ∈ Finset.Icc 1 Ap,
                |coefficient (Real.exp (etaP / L)) a| /
                  (p : ℝ) ^ max r a) *
              (∑ b ∈ Finset.Icc 1 Aq,
                |coefficient (Real.exp (etaQ / L)) b| /
                  (q : ℝ) ^ max s b) := by
            conv_lhs =>
              rw [← Finset.sum_mul]
              congr
              rw [← Finset.mul_sum]
        norm_num only [Nat.cast_pow]
  rw [hdecomp]
  exact (abs_add_three SP SQ SPQ).trans (by
    simpa only [pairRestorationError] using add_le_add_three hSP hSQ hSPQ)







end

end Erdos390.Full.TwoLocalRestorationBound

end

universe u_1
theorem solution :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] (nu : Erdos390.Full.FiniteProbability.{u_1} Omega)
  (value : Omega → Nat) {p q Ap Aq r s : Nat} {etaP etaQ L G : Real},
  (∀ (u v : Nat),
      LE.le.{0}
        (Erdos390.Full.FiniteProbability.expect.{u_1} nu fun omega =>
          Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v) (value omega))
        (HDiv.hDiv.{0, 0, 0} G (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) u) (HPow.hPow.{0, 0, 0} (↑q) v)))) →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0}
          (Erdos390.Full.TwoLocalRestorationBound.pairRestoredNumerator.{u_1} nu value p q Ap Aq etaP etaQ L r s)
          (Erdos390.Full.FiniteProbability.expect.{u_1} nu fun omega =>
            Erdos390.Full.ArithmeticModel.divInd (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s)
              (value omega))))
      (Erdos390.Full.TwoLocalRestorationBound.pairRestorationError p q Ap Aq r s etaP etaQ L G) := by
  exact @Erdos390.Full.TwoLocalRestorationBound.abs_pairRestoredNumerator_sub_expect_le
