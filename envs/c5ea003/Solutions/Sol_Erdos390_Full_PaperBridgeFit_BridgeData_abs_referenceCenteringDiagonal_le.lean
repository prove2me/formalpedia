-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringDiagonal_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:13:59.369768+00:00
-- url     : https://prove2.me/submissions/46e65211-c363-4d52-bca1-cc9648a180b0

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Lemma84 -/
section


/-!
# The finite-dimensional core of Lemma 8.4

This file formalizes only the algebraic part of the moving-low-cell
arithmetic quotient argument.  The Poisson--Dickman gap, prime
quadrature, and marked covariance estimates occur below as fields of an
explicit input structure.  Thus this file contains no postulate claiming
those analytic results.
-/

namespace Erdos390.Lemma84

open scoped BigOperators

noncomputable section

section WeightedBands

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]



namespace WeightedBandData

variable (d : WeightedBandData Prime Band)































































theorem mass_ne_zero (j : Band) : d.mass j ≠ 0 :=
  ne_of_gt (d.mass_pos j)

/-- The definition of the arithmetic band center gives exact weighted
centering on each fiber. -/
theorem center_fiber_sum (j : Band) :
    ∑ p ∈ d.fiber j, d.weight p * (d.center j - d.coord p) = 0 := by
  let H : ℝ := d.mass j
  let N : ℝ := ∑ p ∈ d.fiber j, d.weight p * d.coord p
  have hH : H ≠ 0 := by
    exact d.mass_ne_zero j
  change ∑ p ∈ d.fiber j, d.weight p * (N / H - d.coord p) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hleft :
      (∑ p ∈ d.fiber j, d.weight p * (N / H)) = H * (N / H) := by
    rw [← Finset.sum_mul]
    rfl
  rw [hleft]
  change H * (N / H) - N = 0
  field_simp
  ring



































/-!
## Conditional bridge

The next structure is the exact boundary between the finite argument and
the presently external analytic work.  Its fields are a leading
Poisson--Dickman/quadrature form, an actual marked covariance form, the
nuisance loss, and quantitative comparisons between them.  No field is
the desired quotient conclusion.
-/













end WeightedBandData

end WeightedBands

end

end Erdos390.Lemma84

end

/- Source module: Erdos390.Full.ArithmeticBandGeometry -/
section


/-!
# Exact arithmetic band geometry

This instantiates the finite weighted-band algebra with the paper's actual
prime set, harmonic weights `1/p`, and logarithmic coordinates `t_p`.  In
particular the centering identity is arithmetic, not a continuum identity;
this is the correction required by the audit of Section 8.4.
-/

namespace Erdos390.Full

noncomputable section

open ArithmeticModel

namespace ArithmeticBandGeometry





namespace Partition

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]















/-- Exact arithmetic harmonic centering in each band. -/
theorem center_fiber_sum (P : Partition n W Band) (j : Band) :
    ∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * (P.center j - tPrime n p.1) = 0 := by
  exact P.data.center_fiber_sum j















end Partition

end ArithmeticBandGeometry

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]



































end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

































































/-- Exact arithmetic centering of the compensated prime coefficients on
each actual band.  This is deliberately an identity for the finite prime
set, not a continuum approximation. -/
theorem primeDeviation_fiber_sum (j : Band) :
    ∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * B.primeDeviation p = 0 := by
  calc
    ∑ p ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * B.primeDeviation p =
        ∑ p ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) *
            (B.bandCenter j -
              ArithmeticModel.tPrime B.sampleData.n p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold primeDeviation
      have hpj : B.partition.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
          B.partition.data).mp hp
      rw [hpj]
    _ = 0 := B.partition.center_fiber_sum j















/-! ### Exact main/nuisance coordinate splitting -/

































































































































/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

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

/- Source module: Erdos390.Full.PaperReferenceSharpPrimeGraph -/
section


/-!
# Prime-graph model for the literal sharp reference band operator

The endpoint double-quadrature route loses a factor depending on the first
cell width.  This file instead performs the comparison before band
quadrature.  A band coefficient `alpha_j x_j` is split exactly as

`t_p x_j + (alpha_j - t_p) x_j`.

The first term is a compression of the literal finite prime graph.  The
second is controlled by exact arithmetic centering.  Consequently the
constants below do not involve a least band centre, the number of bands, or
the low-cell width.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic FiniteGraphQuotientInverse
open ConditionedPoissonLimit DickmanBasic
open PoissonDickmanDirichlet
open PaperCanonicalSlowKappa

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





























/-- Exact fiber centering keeps the diagonal replacement error relative in
the sharp norm. -/
theorem abs_referenceCenteringDiagonal_le
    {w CF R : ℝ} (hw : 0 ≤ w) (hCF : 0 ≤ CF) (hR : 0 ≤ R)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |B.referenceCenteringDiagonal x i| ≤ 2 * CF * w * R := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let A : ℝ := H * alpha
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have hA : 0 < A := mul_pos hH halpha
  have hcentered :
      (∑ p ∈ B.partition.data.fiber i,
        (F alpha / (p.1 : ℝ)) * B.primeDeviation p * x i) = 0 := by
    calc
      _ = (F alpha * x i) *
          ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) * B.primeDeviation p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = 0 := by rw [B.primeDeviation_fiber_sum]; ring
  have hrewrite : B.referenceCenteringDiagonal x i =
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          ((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p * x i := by
    unfold referenceCenteringDiagonal
    change (1 / A) *
        (∑ p ∈ B.partition.data.fiber i,
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p * x i) = _
    rw [show (∑ p ∈ B.partition.data.fiber i,
        (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
          B.primeDeviation p * x i) =
      (∑ p ∈ B.partition.data.fiber i,
        ((F (tPrime B.sampleData.n p.1) - F alpha) /
            (p.1 : ℝ)) * B.primeDeviation p * x i) +
      ∑ p ∈ B.partition.data.fiber i,
        (F alpha / (p.1 : ℝ)) * B.primeDeviation p * x i by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring,
      hcentered, add_zero]
  have hterm (p : BandPrime B.sampleData.n B.sampleData.W)
      (hpFiber : p ∈ B.partition.data.fiber i) :
      |((F (tPrime B.sampleData.n p.1) - F alpha) /
          (p.1 : ℝ)) * B.primeDeviation p * x i| ≤
        (CF * w * R) *
          ((1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
    have hpBand : B.partition.band p = i :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
        B.partition.data).mp hpFiber
    have hpcast : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    let d : ℝ := |B.primeDeviation p|
    have hd : 0 ≤ d := abs_nonneg _
    have hdw : d ≤ w := hdevSup p
    have hF : |F (tPrime B.sampleData.n p.1) - F alpha| ≤ CF * d := by
      simpa only [alpha, hpBand, d] using hFdiff p
    have hFd :
        |F (tPrime B.sampleData.n p.1) - F alpha| * d ≤
          (CF * d) * d := mul_le_mul_of_nonneg_right hF hd
    have hCFdw : CF * d ≤ CF * w :=
      mul_le_mul_of_nonneg_left hdw hCF
    have hquad :
        |F (tPrime B.sampleData.n p.1) - F alpha| * d ≤
          (CF * w) * d :=
      hFd.trans (mul_le_mul_of_nonneg_right hCFdw hd)
    have hinv : 0 ≤ 1 / (p.1 : ℝ) := one_div_nonneg.mpr hpcast.le
    have hcoef := mul_le_mul_of_nonneg_left hquad hinv
    have hcoefNonneg : 0 ≤ (1 / (p.1 : ℝ)) * ((CF * w) * d) :=
      mul_nonneg hinv (mul_nonneg (mul_nonneg hCF hw) hd)
    have hscaled := mul_le_mul hcoef (hx i) (abs_nonneg _) hcoefNonneg
    calc
      |((F (tPrime B.sampleData.n p.1) - F alpha) /
          (p.1 : ℝ)) * B.primeDeviation p * x i| =
        ((1 / (p.1 : ℝ)) *
          (|F (tPrime B.sampleData.n p.1) - F alpha| * d)) *
            |x i| := by
          dsimp only [d]
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hpcast]
          ring
      _ ≤ ((1 / (p.1 : ℝ)) * ((CF * w) * d)) * R := hscaled
      _ = (CF * w * R) * ((1 / (p.1 : ℝ)) * d) := by ring
  rw [hrewrite, abs_mul, abs_of_pos (one_div_pos.mpr hA)]
  calc
    (1 / A) *
        |∑ p ∈ B.partition.data.fiber i,
          ((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p * x i| ≤
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          |((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p * x i| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (one_div_nonneg.mpr hA.le)
    _ ≤ (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          (CF * w * R) *
            ((1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
      exact Finset.sum_le_sum fun p hp ↦ hterm p hp
    _ = (1 / A) * (CF * w * R) *
        (∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (1 / A) * (CF * w * R) * (2 * H * alpha) := by
      exact mul_le_mul_of_nonneg_left
        (B.bandDeviationL1_le_two_mul_mass_mul_center i)
        (mul_nonneg (one_div_nonneg.mpr hA.le)
          (mul_nonneg (mul_nonneg hCF hw) hR))
    _ = 2 * CF * w * R := by
      dsimp only [A]
      field_simp [ne_of_gt hH, ne_of_gt halpha]









end BridgeData
end
end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {w CF R : Real},
  LE.le.{0} (0 : Real) w →
    LE.le.{0} (0 : Real) CF →
      LE.le.{0} (0 : Real) R →
        (∀
            (p :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.DickmanBasic.F
                    (Erdos390.Full.ArithmeticModel.tPrime
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      ↑p))
                  (Erdos390.Full.DickmanBasic.F
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B
                      (Erdos390.Full.ArithmeticBandGeometry.Partition.band.{u_2}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p)))))
              (HMul.hMul.{0, 0, 0} CF
                (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)))) →
          (∀
              (p :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)) w) →
            ∀ (x : Band → Real),
              (∀ (j : Band), LE.le.{0} (abs.{0} (x j)) R) →
                ∀ (i : Band),
                  LE.le.{0}
                    (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.referenceCenteringDiagonal.{u_1, u_2} B x i))
                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) CF) w) R) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceCenteringDiagonal_le
