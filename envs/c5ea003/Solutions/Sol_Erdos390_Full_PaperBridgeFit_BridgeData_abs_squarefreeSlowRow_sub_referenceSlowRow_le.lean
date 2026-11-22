-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_squarefreeSlowRow_sub_referenceSlowRow_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:13:47.584295+00:00
-- url     : https://prove2.me/submissions/538d9a85-b386-467f-bf26-178679dab74a

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

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]













theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring







theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]



end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}













































end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperPrimeDeviationGeometry -/
section


/-!
# Deterministic geometry of the actual prime deviations

These are the finite inequalities used in the `L¹` and variance census of
Lemma 8.6.  They apply to the actual arithmetic centers and actual primes.
No continuum center and no prime-number estimate occurs here; analytic
quadrature can therefore be inserted afterwards without a centering error.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PositiveCellTransfer KernelPrimeQuadrature

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



















/-- A sharper low-cell estimate: nonnegativity and exact arithmetic
centering alone give `sum |alpha-t|/p ≤ 2 H alpha`. -/
theorem bandDeviationL1_le_two_mul_mass_mul_center (j : Band) :
    B.bandDeviationL1 j ≤
      2 * B.harmonicMass j * B.bandCenter j := by
  have hfirst :
      (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        B.harmonicMass j * B.bandCenter j := by
    change (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass j *
        ((∑ p ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass j)
    field_simp [ne_of_gt (B.partition.data.mass_pos j)]
  have hmass :
      (∑ p ∈ B.partition.data.fiber j, 1 / (p.1 : ℝ)) =
        B.harmonicMass j := by
    rfl
  unfold bandDeviationL1
  calc
    (∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * |B.primeDeviation p|) ≤
      ∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (B.bandCenter j + tPrime B.sampleData.n p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpj : B.partition.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
          B.partition.data).mp hp
      have hcenter0 := (B.bandCenter_pos j).le
      have ht0 := (B.bandPrime_tPrime_pos p).le
      rw [primeDeviation, hpj]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.2
        ⟨by linarith, by linarith⟩) (by positivity)
    _ = 2 * B.harmonicMass j * B.bandCenter j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, hfirst]
      ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepSlowRightLedger -/
section


/-!
# Exact non-step prime-power ledger for the slow right row

The slow coefficient is the literal arithmetic deviation
`g_p = alpha_{j(p)} - t_p`; it is not replaced by a step function.  This
file keeps the `t_p` factors in the three `JI/IJ/JJ` orientations until
after the output-band average.  The resulting finite estimate has exactly
three kinds of terms:

* a structural `Cpow / W` multiple of `w * alpha_i`;
* an analytic remainder `epsilon / W` times `w` (to be divided by the
  actual arithmetic centre only in the eventual specialization); and
* the literal local reciprocal-square deviation ledger.

No mesh, continuum centre, asymptotic profile, or ODE box occurs in the
theorem below.  It is therefore reusable in both Lemma 8.6 and Proposition
8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

namespace BridgeData





variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















/-- Exact identification of the full and squarefree raw slow rows with the
literal covariance rows on the actual tilted sample. -/
theorem normalizedSlowRows_eq_fullSquarefreeCoefficientRows
    [Nonempty Head] (xi : B.ParamSpace) (i : Band) :
    B.normalizedBandCovarianceRow xi B.slowScore i =
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                (B.actualValuationLaw xi).covVV p.1 q.1 ∧
      B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i =
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                (B.actualValuationLaw xi).covII p.1 q.1 := by
  constructor
  · unfold normalizedBandCovarianceRow bandScore slowScore
      actualValuationLaw BoundedValuationLaw.covVV BoundedValuationLaw.V
    rw [FiniteProbability.covariance_sum_left]
    simp_rw [FiniteProbability.covariance_sum_right,
      FiniteProbability.covariance_smul_right]
    ring
  · unfold normalizedSquarefreeBandCovarianceRow squarefreeBandScore
      slowSquarefreeScore
      actualValuationLaw BoundedValuationLaw.covII BoundedValuationLaw.I
    rw [FiniteProbability.covariance_sum_left]
    simp_rw [FiniteProbability.covariance_sum_right,
      FiniteProbability.covariance_smul_right]
    ring





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperNonstepSquarefreeSlowLedger -/
section


/-!
# Exact non-step squarefree slow-row ledger

This file keeps the primewise coefficient
`g_p = alpha_{j(p)} - t_p` throughout the signed squarefree comparison.
Consequently the off-diagonal profile error is charged to the global
weighted `L¹` deviation, and the `p^{-2}` diagonal is exactly the local
quantity handled by `PaperCanonicalNonstepLocalDiagonalEventually`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperActualSlowRightRowFinite
open SquarefreeReferenceOperatorIdentification

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





set_option maxHeartbeats 2000000 in
/-- Exact entrywise-to-row aggregation for the literal non-step coefficient.
No least-centre divisor and no number-of-bands factor occurs. -/
theorem abs_squarefreeSlowRow_sub_referenceSlowRow_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    {epsilonOff epsilonDiag Cdiag w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonDiag : 0 ≤ epsilonDiag)
    (hentry : ∀ p q : BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 q.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 q.1| ≤
        epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
          else 0))
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i -
        B.referenceSlowRow i| ≤
      7 * epsilonOff * w +
        2 * epsilonDiag * B.bandCenter i +
        Cdiag * B.bandDeviationReciprocalSquare i := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let L1 : ℝ := B.primeDeviationL1
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            ((B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1)| ≤
        epsilonOff / (p.1 : ℝ) * L1 +
          epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
          Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by
    calc
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            ((B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1)| ≤
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q *
              ((B.actualValuationLaw xi).covII p.1 q.1 -
                squarefreeReferenceEntry B.sampleData.n p.1 q.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q| *
            |(B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1| := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [abs_mul]
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q| *
            (epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
              (if p = q then
                epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
              else 0)) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact mul_le_mul_of_nonneg_left (hentry p q) (abs_nonneg _)
      _ = epsilonOff / (p.1 : ℝ) * L1 +
          epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
          Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by
        have hoff :
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q| *
                (epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)))) =
              epsilonOff / (p.1 : ℝ) * L1 := by
          dsimp only [L1]
          unfold primeDeviationL1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _hq
          field_simp [ne_of_gt (hpPos p), ne_of_gt (hpPos q)]
        have hdiag :
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q| *
                (if p = q then
                  epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
                else 0)) =
              epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
                Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by
          calc
            _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                if q = p then
                  |B.primeDeviation q| *
                    (epsilonDiag / (p.1 : ℝ) +
                      Cdiag / (p.1 : ℝ) ^ 2)
                else 0 := by
              apply Finset.sum_congr rfl
              intro q _hq
              by_cases hpq : p = q
              · subst q
                simp
              · have hqp : q ≠ p := fun h ↦ hpq h.symm
                simp [hpq, hqp]
            _ = |B.primeDeviation p| *
                (epsilonDiag / (p.1 : ℝ) +
                  Cdiag / (p.1 : ℝ) ^ 2) := by simp
            _ = epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
                Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by ring
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hoff, hdiag]
        ring
  let A : ℝ := ∑ p ∈ B.partition.data.fiber i,
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      B.primeDeviation q * (B.actualValuationLaw xi).covII p.1 q.1
  let R : ℝ := ∑ p ∈ B.partition.data.fiber i,
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      B.primeDeviation q *
        squarefreeReferenceEntry B.sampleData.n p.1 q.1
  have hdiff : A - R =
      ∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            ((B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1) := by
    dsimp only [A, R]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  have hsum : |A - R| ≤
      epsilonOff * L1 * H +
        epsilonDiag * (2 * H * alpha) +
        Cdiag *
          (∑ p ∈ B.partition.data.fiber i,
            |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
    rw [hdiff]
    calc
      |∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q *
              ((B.actualValuationLaw xi).covII p.1 q.1 -
                squarefreeReferenceEntry B.sampleData.n p.1 q.1)| ≤
          ∑ p ∈ B.partition.data.fiber i,
            |∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                ((B.actualValuationLaw xi).covII p.1 q.1 -
                  squarefreeReferenceEntry B.sampleData.n p.1 q.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ B.partition.data.fiber i,
          (epsilonOff / (p.1 : ℝ) * L1 +
            epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
            Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2) :=
        Finset.sum_le_sum fun p _hp ↦ hinner p
      _ = epsilonOff * L1 * H +
          epsilonDiag *
            (∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ)) * |B.primeDeviation p|) +
          Cdiag *
            (∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
        dsimp only [H, harmonicMass]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hoffsum :
            (∑ p ∈ B.partition.data.fiber i,
              epsilonOff / (p.1 : ℝ) * L1) =
              epsilonOff * L1 *
                ∑ p ∈ B.partition.data.fiber i, 1 / (p.1 : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        have hepssum :
            (∑ p ∈ B.partition.data.fiber i,
              epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ)) =
              epsilonDiag *
                ∑ p ∈ B.partition.data.fiber i,
                  (1 / (p.1 : ℝ)) * |B.primeDeviation p| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        have hCsum :
            (∑ p ∈ B.partition.data.fiber i,
              Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2) =
              Cdiag *
                ∑ p ∈ B.partition.data.fiber i,
                  |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        rw [hoffsum, hepssum, hCsum]
        simp only [Erdos390.Lemma84.WeightedBandData.mass,
          ArithmeticBandGeometry.Partition.data]
      _ ≤ epsilonOff * L1 * H +
          epsilonDiag * (2 * H * alpha) +
          Cdiag *
            (∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
        have hmid :
            epsilonDiag *
                (∑ p ∈ B.partition.data.fiber i,
                  (1 / (p.1 : ℝ)) * |B.primeDeviation p|) ≤
              epsilonDiag * (2 * H * alpha) := by
          simpa only [bandDeviationL1, H, alpha] using
            mul_le_mul_of_nonneg_left
              (B.bandDeviationL1_le_two_mul_mass_mul_center i)
              hepsilonDiag
        exact add_le_add (add_le_add le_rfl hmid) le_rfl
  have hactual :=
    (B.normalizedSlowRows_eq_fullSquarefreeCoefficientRows xi i).2
  have hscaled :
      |(1 / H) * A - (1 / H) * R| ≤
        epsilonOff * L1 + 2 * epsilonDiag * alpha +
          Cdiag * B.bandDeviationReciprocalSquare i := by
    rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hH)]
    have hscaled0 :=
      mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hH.le)
    unfold bandDeviationReciprocalSquare
    dsimp only [H, alpha, harmonicMass] at hH hscaled0 ⊢
    convert hscaled0 using 1
    all_goals field_simp [hH.ne']
  have hL1 : epsilonOff * L1 ≤ 7 * epsilonOff * w := by
    calc
      epsilonOff * L1 ≤ epsilonOff * (7 * w) :=
        mul_le_mul_of_nonneg_left hdevL1 hepsilonOff
      _ = 7 * epsilonOff * w := by ring
  rw [hactual]
  change |(1 / H) * A - (1 / H) * R| ≤ _
  exact hscaled.trans (add_le_add (add_le_add hL1 le_rfl) le_rfl)







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) {epsilonOff epsilonDiag Cdiag w : Real},
  LE.le.{0} (0 : Real) epsilonOff →
    LE.le.{0} (0 : Real) epsilonDiag →
      (∀
          (p q :
            Erdos390.Full.ArithmeticBandGeometry.BandPrime
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
          LE.le.{0}
            (abs.{0}
              (HSub.hSub.{0, 0, 0}
                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q)
                (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  ↑p ↑q)))
            (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonOff (HMul.hMul.{0, 0, 0} ↑↑p ↑↑q))
              (ite.{1} (Eq.{1} p q)
                (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} epsilonDiag ↑↑p)
                  (HDiv.hDiv.{0, 0, 0} Cdiag (HPow.hPow.{0, 0, 0} ↑↑p (2 : Nat))))
                (0 : Real)))) →
        LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
            (HMul.hMul.{0, 0, 0} (7 : Real) w) →
          ∀ (i : Band),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedSquarefreeBandCovarianceRow.{u_1, u_2} B xi
                    (Erdos390.Full.PaperBridgeFit.BridgeData.slowSquarefreeScore.{u_1, u_2} B) i)
                  (Erdos390.Full.PaperBridgeFit.BridgeData.referenceSlowRow.{u_1, u_2} B i)))
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (7 : Real) epsilonOff) w)
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) epsilonDiag)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)))
                (HMul.hMul.{0, 0, 0} Cdiag
                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandDeviationReciprocalSquare.{u_1, u_2} B i))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_squarefreeSlowRow_sub_referenceSlowRow_le
