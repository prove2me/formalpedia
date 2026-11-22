-- Prove2me | solution 1 for Erdos390.Full.SquarefreeSharpBandTransfer.abs_squarefreeSharpRow_sub_referenceSharpRow_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:32:45.079793+00:00
-- url     : https://prove2.me/submissions/628cb9c3-5740-4330-afcb-bf83c719c9cc

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PaperCompensatedCoefficientBounds -/
section


/-!
# Actual compensated-prime coefficient bounds for Lemma 8.6

This file specializes the elementary coefficient ledger to the literal
arithmetic prime partition.  The regression vector is an element of the
paper's exact arithmetic gauge

`sum_j H_j * alpha_j * q_j = 0`,

and the compensated coefficient is literally
`c_p = (alpha_{j(p)} - t_p) - q_{j(p)}`.  Thus none of the three norms below
is represented by an abstract array or stored in a certificate.

The sole regression input is the sharp norm estimate produced by the
weighted inverse and the row estimate.  All remaining estimates are derived
from the actual prime sums and the already proved canonical-mesh moment
bounds.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)

























/-- Exact first-moment identity for the arithmetic centers. -/
theorem sum_mass_mul_center_eq_bandTReciprocalSum :
    (∑ j : Band, P.mass j * P.center j) =
      bandTReciprocalSum n W := by
  have hcenter (j : Band) :
      P.mass j * P.center j =
        ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    change P.data.mass j *
        ((∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
    field_simp [ne_of_gt (P.data.mass_pos j)]
  calc
    (∑ j : Band, P.mass j * P.center j) =
        ∑ j : Band, ∑ p ∈ P.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hcenter j
    _ = ∑ p : BandPrime n W,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
            rw [← Finset.sum_fiberwise Finset.univ P.band
              (fun p : BandPrime n W ↦
                (1 / (p.1 : ℝ)) * tPrime n p.1)]
            apply Finset.sum_congr rfl
            intro j hj
            rfl
    _ = bandTReciprocalSum n W := by
          unfold bandTReciprocalSum
          have hattach := Finset.sum_attach (primeBand n W)
            (fun p ↦ tPrime n p / (p : ℝ))
          rw [← hattach]
          apply Finset.sum_congr rfl
          intro p hp
          ring













end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.SquarefreeSharpBandTransfer -/
section


/-!
# Sharp band aggregation of the signed squarefree comparison

This is the exact finite aggregation needed between the marked-divisor
profiles and the canonical endpoint operator.  The moving low row is kept
visible: a profile error `epsilon` costs `epsilon / alpha_i`, whereas the
diagonal Bernoulli correction costs only `Cdiag / W`.
-/

open scoped BigOperators

namespace Erdos390.Full.SquarefreeSharpBandTransfer

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {Omega Band : Type*} [Fintype Omega]
  [Fintype Band] [DecidableEq Band]
  {M n W : ℕ}









/-- The exact sharp-row aggregation.  No minimum center or dimension factor
is introduced. -/
theorem abs_squarefreeSharpRow_sub_referenceSharpRow_le
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (hn : 1 < n) (hW : 1 < W)
    {epsilonOff epsilonDiag Cdiag : ℝ}
    (hCdiag : 0 ≤ Cdiag)
    (hentry : ∀ p q : BandPrime n W,
      |law.covII p.1 q.1 - squarefreeReferenceEntry n p.1 q.1| ≤
        epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
          else 0))
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |squarefreeSharpRow law P q i - referenceSharpRow P q i| ≤
      epsilonOff * bandTReciprocalSum n W / P.center i +
        epsilonDiag + Cdiag * (1 / (W : ℝ)) := by
  have hmass : 0 < P.mass i := P.data.mass_pos i
  have hcenter : 0 < P.center i := P.center_pos hn i
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hprimePos (p : BandPrime n W) : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hprimeW (p : BandPrime n W) : (W : ℝ) ≤ p.1 := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le
  have hcenterNonneg (j : Band) : 0 ≤ P.center j :=
    (P.center_pos hn j).le
  have hcoeff (j : Band) : |P.center j * q j| ≤ P.center j := by
    rw [abs_mul, abs_of_nonneg (hcenterNonneg j)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hq j) (hcenterNonneg j)
  have htotal :
      (∑ r : BandPrime n W, P.center (P.band r) / (r.1 : ℝ)) =
        bandTReciprocalSum n W := by
    calc
      (∑ r : BandPrime n W, P.center (P.band r) / (r.1 : ℝ)) =
          ∑ j : Band, P.mass j * P.center j := by
        rw [← Finset.sum_fiberwise Finset.univ P.band
          (fun r : BandPrime n W ↦ P.center (P.band r) / (r.1 : ℝ))]
        apply Finset.sum_congr rfl
        intro j hj
        change (∑ r ∈ P.data.fiber j,
            P.center (P.band r) / (r.1 : ℝ)) = P.mass j * P.center j
        have hband : ∀ r ∈ P.data.fiber j, P.band r = j := by
          intro r hr
          simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
            using hr
        calc
          (∑ r ∈ P.data.fiber j,
              P.center (P.band r) / (r.1 : ℝ)) =
              ∑ r ∈ P.data.fiber j,
                (1 / (r.1 : ℝ)) * P.center j := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hband r hr]
            ring
          _ = P.mass j * P.center j := by
            rw [← Finset.sum_mul]
            rfl
      _ = bandTReciprocalSum n W :=
        P.sum_mass_mul_center_eq_bandTReciprocalSum
  have hinner (p : BandPrime n W) :
      (∑ r : BandPrime n W,
        |P.center (P.band r) * q (P.band r)| *
          |law.covII p.1 r.1 - squarefreeReferenceEntry n p.1 r.1|) ≤
        epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W +
          epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
          Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ r : BandPrime n W,
          P.center (P.band r) *
            (epsilonOff / ((p.1 : ℝ) * (r.1 : ℝ)) +
              (if p = r then
                epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
              else 0)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul (hcoeff (P.band r)) (hentry p r)
          (abs_nonneg _) (hcenterNonneg (P.band r))
      _ = epsilonOff / (p.1 : ℝ) *
            (∑ r : BandPrime n W,
              P.center (P.band r) / (r.1 : ℝ)) +
          epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
          Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2 := by
        have hoffsum :
            (∑ r : BandPrime n W,
              P.center (P.band r) *
                (epsilonOff / ((p.1 : ℝ) * (r.1 : ℝ)))) =
              epsilonOff / (p.1 : ℝ) *
                (∑ r : BandPrime n W,
                  P.center (P.band r) / (r.1 : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          field_simp [ne_of_gt (hprimePos p), ne_of_gt (hprimePos r)]
        have hdiagsum :
            (∑ r : BandPrime n W,
              P.center (P.band r) *
                (if p = r then
                  epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
                else 0)) =
              epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
                Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2 := by
          calc
            _ = ∑ r : BandPrime n W,
                if r = p then
                  P.center (P.band r) *
                    (epsilonDiag / (p.1 : ℝ) +
                      Cdiag / (p.1 : ℝ) ^ 2)
                else 0 := by
              apply Finset.sum_congr rfl
              intro r hr
              by_cases hpr : p = r
              · subst r
                simp
              · have hrp : r ≠ p := fun h ↦ hpr h.symm
                simp [hpr, hrp]
            _ = P.center (P.band p) *
                  (epsilonDiag / (p.1 : ℝ) +
                    Cdiag / (p.1 : ℝ) ^ 2) := by
              simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
            _ = epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
                Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2 := by ring
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hoffsum, hdiagsum]
        ring
      _ = epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W +
          epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
          Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2 := by rw [htotal]
  have hfiberBand (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
      P.band p = i := by
    simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
  have hdiagSum :
      (∑ p ∈ P.data.fiber i,
        (epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
          Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2)) ≤
        (epsilonDiag * P.center i +
          Cdiag * P.center i * (1 / (W : ℝ))) * P.mass i := by
    calc
      _ ≤ ∑ p ∈ P.data.fiber i,
          (epsilonDiag * P.center i +
            Cdiag * P.center i * (1 / (W : ℝ))) *
              (1 / (p.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [hfiberBand p hp]
        have hratio : 1 / (p.1 : ℝ) ≤ 1 / (W : ℝ) := by
          exact one_div_le_one_div_of_le hWpos (hprimeW p)
        have hbase : 0 ≤ Cdiag * P.center i * (1 / (p.1 : ℝ)) := by
          positivity
        have hpow : Cdiag * P.center i / (p.1 : ℝ) ^ 2 ≤
            (Cdiag * P.center i * (1 / (W : ℝ))) *
              (1 / (p.1 : ℝ)) := by
          calc
            Cdiag * P.center i / (p.1 : ℝ) ^ 2 =
                (Cdiag * P.center i * (1 / (p.1 : ℝ))) *
                  (1 / (p.1 : ℝ)) := by ring
            _ ≤ (Cdiag * P.center i * (1 / (p.1 : ℝ))) *
                  (1 / (W : ℝ)) :=
              mul_le_mul_of_nonneg_left hratio hbase
            _ = (Cdiag * P.center i * (1 / (W : ℝ))) *
                  (1 / (p.1 : ℝ)) := by ring
        calc
          epsilonDiag * P.center i / (p.1 : ℝ) +
              Cdiag * P.center i / (p.1 : ℝ) ^ 2 ≤
            epsilonDiag * P.center i / (p.1 : ℝ) +
              (Cdiag * P.center i * (1 / (W : ℝ))) *
                (1 / (p.1 : ℝ)) :=
            add_le_add (le_refl _) hpow
          _ = (epsilonDiag * P.center i +
                Cdiag * P.center i * (1 / (W : ℝ))) *
              (1 / (p.1 : ℝ)) := by ring
      _ = (epsilonDiag * P.center i +
          Cdiag * P.center i * (1 / (W : ℝ))) * P.mass i := by
        rw [← Finset.mul_sum]
        rfl
  unfold squarefreeSharpRow referenceSharpRow squarefreeBandRow referenceBandRow
  rw [← sub_div]
  have hraw :
      |(1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covII p.1 r.1) -
        (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) *
                squarefreeReferenceEntry n p.1 r.1)| ≤
      epsilonOff * bandTReciprocalSum n W +
        epsilonDiag * P.center i +
          Cdiag * P.center i * (1 / (W : ℝ)) := by
    let A : ℝ := ∑ p ∈ P.data.fiber i,
      ∑ r : BandPrime n W,
        P.center (P.band r) * q (P.band r) * law.covII p.1 r.1
    let R : ℝ := ∑ p ∈ P.data.fiber i,
      ∑ r : BandPrime n W,
        P.center (P.band r) * q (P.band r) *
          squarefreeReferenceEntry n p.1 r.1
    have hdiff : A - R =
        ∑ p ∈ P.data.fiber i,
          ∑ r : BandPrime n W,
            P.center (P.band r) * q (P.band r) *
              (law.covII p.1 r.1 -
                squarefreeReferenceEntry n p.1 r.1) := by
      dsimp only [A, R]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have habsInner (p : BandPrime n W) :
        |∑ r : BandPrime n W,
            P.center (P.band r) * q (P.band r) *
              (law.covII p.1 r.1 -
                squarefreeReferenceEntry n p.1 r.1)| ≤
          epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W +
            epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
            Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2 := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            |P.center (P.band r) * q (P.band r) *
              (law.covII p.1 r.1 -
                squarefreeReferenceEntry n p.1 r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ r : BandPrime n W,
            |P.center (P.band r) * q (P.band r)| *
              |law.covII p.1 r.1 -
                squarefreeReferenceEntry n p.1 r.1| := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [abs_mul]
        _ ≤ _ := hinner p
    have hsumBound : |A - R| ≤
        epsilonOff * bandTReciprocalSum n W * P.mass i +
          (epsilonDiag * P.center i +
            Cdiag * P.center i * (1 / (W : ℝ))) * P.mass i := by
      rw [hdiff]
      calc
        _ ≤ ∑ p ∈ P.data.fiber i,
            |∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) *
                (law.covII p.1 r.1 -
                  squarefreeReferenceEntry n p.1 r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ P.data.fiber i,
            (epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W +
              epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
              Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2) := by
          exact Finset.sum_le_sum fun p hp ↦ habsInner p
        _ = (∑ p ∈ P.data.fiber i,
              epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W) +
            (∑ p ∈ P.data.fiber i,
              (epsilonDiag * P.center (P.band p) / (p.1 : ℝ) +
                Cdiag * P.center (P.band p) / (p.1 : ℝ) ^ 2)) := by
          simp only [Finset.sum_add_distrib]
          ring
        _ ≤ epsilonOff * bandTReciprocalSum n W * P.mass i +
            (epsilonDiag * P.center i +
              Cdiag * P.center i * (1 / (W : ℝ))) * P.mass i := by
          apply add_le_add
          · change (∑ p ∈ P.data.fiber i,
                epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W) ≤ _
            have hoffFiber :
              (∑ p ∈ P.data.fiber i,
                  epsilonOff / (p.1 : ℝ) * bandTReciprocalSum n W) =
                  epsilonOff * bandTReciprocalSum n W *
                    (∑ p ∈ P.data.fiber i, 1 / (p.1 : ℝ)) := by
                symm
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p hp
                ring
            rw [hoffFiber]
            rfl
          · exact hdiagSum
    have hscaled :
        |(1 / P.mass i) * A - (1 / P.mass i) * R| =
          (1 / P.mass i) * |A - R| := by
      rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hmass)]
    change |(1 / P.mass i) * A - (1 / P.mass i) * R| ≤ _
    rw [hscaled]
    calc
      (1 / P.mass i) * |A - R| ≤
          (1 / P.mass i) *
            (epsilonOff * bandTReciprocalSum n W * P.mass i +
              (epsilonDiag * P.center i +
                Cdiag * P.center i * (1 / (W : ℝ))) * P.mass i) := by
        exact mul_le_mul_of_nonneg_left hsumBound
          (one_div_nonneg.mpr hmass.le)
      _ = epsilonOff * bandTReciprocalSum n W +
          epsilonDiag * P.center i +
            Cdiag * P.center i * (1 / (W : ℝ)) := by
        field_simp [hmass.ne']
        ring
  rw [abs_div, abs_of_pos hcenter]
  calc
    _ ≤ (epsilonOff * bandTReciprocalSum n W +
        epsilonDiag * P.center i +
          Cdiag * P.center i * (1 / (W : ℝ))) / P.center i :=
      div_le_div_of_nonneg_right hraw hcenter.le
    _ = epsilonOff * bandTReciprocalSum n W / P.center i +
        epsilonDiag + Cdiag * (1 / (W : ℝ)) := by
      field_simp [hcenter.ne']

end

end Erdos390.Full.SquarefreeSharpBandTransfer

end

universe u_1 u_2
theorem solution :
∀ {Omega : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Omega] [inst_1 : Fintype.{u_2} Band]
  [inst_2 : DecidableEq.{u_2 + 1} Band] {M n W : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M)
  (P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_2} n W Band),
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      ∀ {epsilonOff epsilonDiag Cdiag : Real},
        LE.le.{0} (0 : Real) Cdiag →
          (∀ (p q : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W),
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1} law ↑p ↑q)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry n ↑p ↑q)))
                (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonOff (HMul.hMul.{0, 0, 0} ↑↑p ↑↑q))
                  (ite.{1} (Eq.{1} p q)
                    (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonDiag ↑↑p)
                      (HDiv.hDiv.{0, 0, 0} Cdiag (HPow.hPow.{0, 0, 0} ↑↑p (2 : Nat))))
                    (0 : Real)))) →
            ∀ (q : Band → Real),
              (∀ (j : Band), LE.le.{0} (abs.{0} (q j)) (1 : Real)) →
                ∀ (i : Band),
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.SquarefreeSharpBandTransfer.squarefreeSharpRow.{u_1, u_2} law P q i)
                        (Erdos390.Full.SquarefreeSharpBandTransfer.referenceSharpRow.{u_2} P q i)))
                    (HAdd.hAdd.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HDiv.hDiv.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} epsilonOff (Erdos390.Full.PrimeSums.bandTReciprocalSum n W))
                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2} P i))
                        epsilonDiag)
                      (HMul.hMul.{0, 0, 0} Cdiag (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))) := by
  exact @Erdos390.Full.SquarefreeSharpBandTransfer.abs_squarefreeSharpRow_sub_referenceSharpRow_le
