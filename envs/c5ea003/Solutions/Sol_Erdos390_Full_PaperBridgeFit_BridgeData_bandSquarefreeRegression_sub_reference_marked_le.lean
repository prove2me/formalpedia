-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.bandSquarefreeRegression_sub_reference_marked_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:18:24.425874+00:00
-- url     : https://prove2.me/submissions/771a7d6a-567c-49e9-aca7-9c12190f974a

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















theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]











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

/- Source module: Erdos390.Full.PaperActualCompensatedRegression -/
section


/-!
# The actual two-stage compensated regression in Lemma 8.6

The objects in this file live on the genuine guard-deleted, tilted finite
probability space from `PaperBridgeFit`.  In particular, the nuisance
coefficient is not an abstract vector satisfying a normal equation: it is
defined by applying the inverse of the proved actual nuisance covariance
operator to the literal covariance vector of the post-band-regression score.

This file proves the exact finite identities used before the analytic
`w^2` comparison: the prime-coefficient expansion, nuisance normal equation,
orthogonality, Schur variance identity, and marked-row decomposition.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















/-- Reindexing over the actual partition identifies the raw band score with
the corresponding primewise coefficient sum. -/
theorem bandRegressionScore_eq_primeSum
    (q : B.RawBandGauge) (m : B.sampleData.Sample) :
    B.bandRegressionScore q m =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandRegressionCoefficient q p *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandRegressionScore bandScore bandRegressionCoefficient
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      q.1 (B.partition.band p) *
        valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  rw [hpj]

















































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperExactTwoStageOrdinaryFast -/
section


/-!
# Ordinary-fast / sharp-slow form of the exact two-stage solve

The fast target in Proposition 8.7 is bounded in the ordinary raw-band
supremum norm: its unprojected coordinates are
`(L / q) * Delta_j / H_j = O(1)`.  They are not, in general, bounded after
division by the moving centre `alpha_j`; in particular `alpha_0 -> 0`.

The slow regression is different.  Lemma 8.5 supplies a sharp inverse for
that right-hand side and hence a regression vector of size `O(w alpha_j)`.
This file records the exact finite algebra with those two norms kept
separate.  It is the norm-correct form of the block calculation in the
proof of Proposition 8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
  MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Summing the literal band masses recovers the full reciprocal mass of
the actual prime band.  This exposes the sole `log L` loss in the ordinary
fast nuisance row. -/
theorem sum_harmonicMass_eq_bandReciprocalSum :
    (∑ j : Band, B.harmonicMass j) =
      PrimeSums.bandReciprocalSum B.sampleData.n B.sampleData.W := by
  calc
    (∑ j : Band, B.harmonicMass j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          (1 / (p.1 : ℝ)) := by
      unfold harmonicMass ArithmeticBandGeometry.Partition.mass
        Erdos390.Lemma84.WeightedBandData.mass
      rw [← Finset.sum_fiberwise Finset.univ B.partition.band
        (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
          (1 / (p.1 : ℝ)))]
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    _ = PrimeSums.bandReciprocalSum
        B.sampleData.n B.sampleData.W := by
      unfold PrimeSums.bandReciprocalSum
      have hattach := Finset.sum_attach
        (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
        (fun p ↦ 1 / (p : ℝ))
      simpa only [Finset.univ_eq_attach] using hattach































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperActualFastMarkedRowProfiles -/
section


/-!
# Ordinary-fast marked rows from the literal analytic inputs

The fast solve is bounded in the ordinary raw-band norm.  Its reference
kernel row is nevertheless `O(1/p)`: the product bound for the Dickman
kernel supplies the missing factor `t_r`, whose prime sum is bounded.  Only
the signed profile error pays the full harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` bookkeeping.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem bandRegression_markedRows_eq_sums [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covVV p r.1 ∧
    (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p r.1 := by
  constructor
  · have hscore : B.bandRegressionScore q =
        fun m ↦ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          q.1 (B.partition.band r) *
            valuation r.1 (B.sampleData.value m) := by
      funext m
      exact B.bandRegressionScore_eq_primeSum q m
    rw [hscore]
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl
  · unfold bandSquarefreeRegressionScore
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl



/-- Signed profile transfer for an ordinary raw-band coefficient.  The
off-diagonal error pays the exact total harmonic mass. -/
theorem bandSquarefreeRegression_sub_reference_marked_le
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond H : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hentry : ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2
          else 0)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q) -
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p r.1| ≤
      ‖q‖ *
        (epsilonOff * H + epsilonDiag +
          epsilonSecond * (1 / (p : ℝ))) * (1 / (p : ℝ)) := by
  rw [(B.bandRegression_markedRows_eq_sums xi q p).2]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hmassEq :
      (∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (1 / (r.1 : ℝ))) = ∑ j : Band, B.harmonicMass j := by
    rw [B.sum_harmonicMass_eq_bandReciprocalSum]
    unfold PrimeSums.bandReciprocalSum
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W) (fun r ↦ 1 / (r : ℝ))
    simpa only [Finset.univ_eq_attach] using hattach
  have hq (r : BandPrime B.sampleData.n B.sampleData.W) :
      |q.1 (B.partition.band r)| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1
      (B.partition.band r)
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covII p r.1 -
          q.1 (B.partition.band r) *
            squarefreeReferenceEntry B.sampleData.n p r.1)| =
      |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          ((B.actualValuationLaw xi).covII p r.1 -
            squarefreeReferenceEntry B.sampleData.n p r.1)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |(B.actualValuationLaw xi).covII p r.1 -
            squarefreeReferenceEntry B.sampleData.n p r.1| := by
      calc
        _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |q.1 (B.partition.band r) *
              ((B.actualValuationLaw xi).covII p r.1 -
                squarefreeReferenceEntry B.sampleData.n p r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ *
          (epsilonOff * (1 / (p : ℝ)) * (1 / (r.1 : ℝ)) +
            if p = r.1 then
              epsilonDiag * (1 / (p : ℝ)) +
                epsilonSecond * (1 / (p : ℝ)) ^ 2
            else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul (hq r) (hentry p r.1 hp r.2)
        (abs_nonneg _) (norm_nonneg q)
    _ = ‖q‖ *
        (epsilonOff * (1 / (p : ℝ)) *
            (∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (1 / (r.1 : ℝ))) +
          epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      have hoff :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            epsilonOff * (1 / (p : ℝ)) * (1 / (r.1 : ℝ))) =
          epsilonOff * (1 / (p : ℝ)) *
            (∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (1 / (r.1 : ℝ))) := by rw [Finset.mul_sum]
      have hdiag :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            if p = r.1 then
              epsilonDiag * (1 / (p : ℝ)) +
                epsilonSecond * (1 / (p : ℝ)) ^ 2
            else 0) =
          epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2 := by
        rw [Finset.sum_eq_single ⟨p, hp⟩]
        · simp
        · intro r hr hne
          have hval : p ≠ r.1 := by
            intro heq
            exact hne (Subtype.ext heq.symm)
          simp only [if_neg hval]
        · exact fun hnot ↦ (hnot (Finset.mem_univ _)).elim
      rw [hoff, hdiag]
      ring
    _ ≤ ‖q‖ *
        (epsilonOff * (1 / (p : ℝ)) * H +
          epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      gcongr
      exact hmassEq.trans_le hH
    _ = ‖q‖ *
        (epsilonOff * H + epsilonDiag +
          epsilonSecond * (1 / (p : ℝ))) * (1 / (p : ℝ)) := by ring





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {epsilonOff epsilonDiag epsilonSecond H : Real},
  LE.le.{0} (0 : Real) epsilonOff →
    LE.le.{0} (∑ j : Band, Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B j) H →
      (∀ (p r : Nat),
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              p →
            Membership.mem.{0, 0}
                (Erdos390.Full.ArithmeticModel.primeBand
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                r →
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) p r)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      p r)))
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)))
                    (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑r : Real)))
                  (ite.{1} (Eq.{1} p r)
                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)))
                      (HMul.hMul.{0, 0, 0} epsilonSecond
                        (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)) (2 : Nat))))
                    (0 : Real)))) →
        ∀ {p : Nat},
          Membership.mem.{0, 0}
              (Erdos390.Full.ArithmeticModel.primeBand
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
              p →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                    (fun
                        (m :
                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                      Erdos390.Full.ArithmeticModel.divInd p
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandSquarefreeRegressionScore.{u_1, u_2} B q))
                  (∑ r :
                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                    HMul.hMul.{0, 0, 0}
                      ((↑q : Band → Real)
                        (Erdos390.Full.ArithmeticBandGeometry.Partition.band.{u_2}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) r))
                      (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        p (↑r : Nat)))))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (Norm.norm.{u_2} q)
                  (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff H) epsilonDiag)
                    (HMul.hMul.{0, 0, 0} epsilonSecond (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real)))))
                (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.bandSquarefreeRegression_sub_reference_marked_le
