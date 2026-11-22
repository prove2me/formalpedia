-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceSlowRow_le_of_harmonicCentering
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:13:33.783644+00:00
-- url     : https://prove2.me/submissions/318e3eac-64bf-4b4b-a955-fdc043f80a71

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
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

/- Source module: Erdos390.Full.PaperPrimePowerRow -/
section


/-!
# The paper prime-band row contraction

This module specializes the actual finite-law contraction to

* the literal band `primeBand n W`,
* `t_p = log p / log y`,
* reciprocal weight `u_p = 1 / p`,
* row normalization `p`, and
* `invW = 1 / W`.

Thus every elementary prime-coordinate and prime-sum input in the final row
step of paper Lemma 7.5 is discharged here.  The remaining hypotheses are
exactly the actual `JI`, `IJ`, `JJ`, diagonal, and endpoint estimates proved
by the marked four-chamber analysis.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRow

open ArithmeticModel Scale PrimeSums
open PrimePowerCovariance PrimePowerRowTransfer

noncomputable section



lemma tPrime_le_one_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    tPrime n p <= 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y hn0]
    nlinarith
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hyfloor : (yNat n : Real) <= y n :=
    Nat.floor_le (le_of_lt (y_pos hn0))
  have hpcast : (p : Real) <= y n := by
    exact (by exact_mod_cast le_yNat_of_mem_primeBand hp :
      (p : Real) <= (yNat n : Real)).trans hyfloor
  have hlog : Real.log (p : Real) <= Real.log (y n) :=
    Real.log_le_log hp0 hpcast
  unfold tPrime
  calc
    Real.log (p : Real) / Real.log (y n) <=
        Real.log (y n) / Real.log (y n) :=
      div_le_div_of_nonneg_right hlog hlogy.le
    _ = 1 := div_self hlogy.ne'





namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000



end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow

end

/- Source module: Erdos390.Full.SquarefreeReferenceOperatorIdentification -/
section


/-!
# Exact identification of the signed squarefree reference operator

The signed reference covariance used in the arithmetic part of paper
Lemma 8.4 is defined prime by prime in
`SquarefreeCovarianceReference`.  The moving-low inverse, on the other
hand, is proved for the endpoint matrix called `arithmeticDiagonal` plus
`arithmeticKernel`.  This file proves that these are literally the same
finite operator for every certified prime partition.  No limit, row bound,
covariance estimate, or inverse is assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.SquarefreeReferenceOperatorIdentification

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PositiveCellTransfer
open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open CompressedArithmeticOperator
open ConditionedPoissonLimit DickmanBasic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : Partition n W Band}







/-- The reference entry is the kernel entry plus a Kronecker diagonal
multiplier. -/
theorem squarefreeReferenceEntry_eq_kernel_add_diagonal
    (p q : ℕ) :
    squarefreeReferenceEntry n p q =
      squarefreeKernelEntry n p q +
        if p = q then F (tPrime n p) / (p : ℝ) else 0 := by
  by_cases hpq : p = q
  · subst q
    simp [squarefreeReferenceEntry]
    ring
  · simp [squarefreeReferenceEntry, hpq]







section MarkedProfileApplication

variable {Cell : Type*} [Fintype Cell]
variable {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
variable {M : ℕ}



end MarkedProfileApplication

end Erdos390.Full.SquarefreeReferenceOperatorIdentification

end

/- Source module: Erdos390.Full.PaperNonstepReferenceSlowDirect -/
section


/-!
# Direct harmonic-centering bound for the non-step reference slow row

This finite lemma avoids a prime-row residual altogether.  The diagonal
identity term cancels exactly because `sum_{p in P_i} g_p/p = 0`.  What
remains is bounded by the local product moment `sum t_p |g_p|/p`; the kernel
term factors into the output first moment and the corresponding global
product moment.  Thus every contribution contains `w * alpha_i` with a
universal constant.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open ConditionedPoissonLimit DickmanBasic

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Direct universal reference bound for the literal non-step coefficient.
No row-residual, least-centre, mesh, or asymptotic hypothesis occurs. -/
theorem abs_referenceSlowRow_le_of_harmonicCentering
    {w CF CKernel : ℝ}
    (hw : 0 ≤ w) (hCKernel : 0 ≤ CKernel)
    (hFone : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) - 1| ≤
        CF * tPrime B.sampleData.n p.1)
    (hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.referenceSlowRow i| ≤
      (CF + 7 * CKernel) * w * B.bandCenter i := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let diagonal : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      B.primeDeviation p *
        (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ))
  let kernel : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))
  let globalProduct : ℝ :=
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
        (1 / (q.1 : ℝ))
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by simpa only [alpha] using B.bandCenter_pos i
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have ht0 (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ tPrime B.sampleData.n p.1 :=
    (B.bandPrime_tPrime_pos p).le
  have ht1 (p : BandPrime B.sampleData.n B.sampleData.W) :
      tPrime B.sampleData.n p.1 ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one p.2
  have hfirstMoment :
      (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        H * alpha := by
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.harmonicMass i * B.bandCenter i
    unfold harmonicMass bandCenter
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass i *
        ((∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass i)
    field_simp [ne_of_gt (B.partition.data.mass_pos i)]
  have hdiagInner (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          (if p.1 = q.1 then
            F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
          else 0)) =
        B.primeDeviation p *
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _hq hqp
      have hpqVal : p.1 ≠ q.1 := by
        intro hpq
        exact hqp (Subtype.ext hpq.symm)
      simp [hpqVal]
    · simp
  have href : B.referenceSlowRow i = diagonal + kernel := by
    unfold referenceSlowRow diagonal kernel H
    simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal, mul_add]
    rw [show
      (∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.primeDeviation q * squarefreeKernelEntry
              B.sampleData.n p.1 q.1 +
            B.primeDeviation q *
              (if p.1 = q.1 then
                F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
              else 0))) =
      (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ))) +
      ∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * squarefreeKernelEntry
            B.sampleData.n p.1 q.1 by
        simp_rw [Finset.sum_add_distrib, hdiagInner]
        ring]
    unfold squarefreeKernelEntry
    ring
  have hcentered :
      (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p * (1 / (p.1 : ℝ))) = 0 := by
    rw [show (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p * (1 / (p.1 : ℝ))) =
      ∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * B.primeDeviation p by
        apply Finset.sum_congr rfl
        intro p _hp
        ring]
    exact B.primeDeviation_fiber_sum i
  have hdiagRewrite : diagonal = (1 / H) *
      ∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          ((F (tPrime B.sampleData.n p.1) - 1) / (p.1 : ℝ)) := by
    unfold diagonal
    rw [show (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ))) =
      (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          ((F (tPrime B.sampleData.n p.1) - 1) / (p.1 : ℝ))) +
      ∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p * (1 / (p.1 : ℝ)) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _hp
        ring,
      hcentered, add_zero]
  have hdiagonal : |diagonal| ≤ (CF * w) * alpha := by
    rw [hdiagRewrite, abs_mul,
      abs_of_nonneg (one_div_nonneg.mpr hH.le)]
    calc
      (1 / H) *
          |∑ p ∈ B.partition.data.fiber i,
            B.primeDeviation p *
              ((F (tPrime B.sampleData.n p.1) - 1) /
                (p.1 : ℝ))| ≤
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            |B.primeDeviation p *
              ((F (tPrime B.sampleData.n p.1) - 1) /
                (p.1 : ℝ))| :=
        mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (CF * w) *
              ((1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        rw [abs_mul, abs_div, abs_of_pos (hpPos p)]
        calc
          |B.primeDeviation p| *
              (|F (tPrime B.sampleData.n p.1) - 1| / (p.1 : ℝ)) ≤
            w * ((CF * tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
              calc
                |B.primeDeviation p| *
                    (|F (tPrime B.sampleData.n p.1) - 1| / (p.1 : ℝ)) ≤
                  w * (|F (tPrime B.sampleData.n p.1) - 1| / (p.1 : ℝ)) :=
                    mul_le_mul_of_nonneg_right (hdevSup p)
                      (div_nonneg (abs_nonneg _) (hpPos p).le)
                _ ≤ w * ((CF * tPrime B.sampleData.n p.1) / (p.1 : ℝ)) :=
                    mul_le_mul_of_nonneg_left
                      (div_le_div_of_nonneg_right (hFone p) (hpPos p).le) hw
          _ = (CF * w) *
              ((1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) := by ring
      _ = (CF * w) * alpha := by
        rw [← Finset.mul_sum, hfirstMoment]
        field_simp [hH.ne']
  have hglobal0 : 0 ≤ globalProduct := by
    dsimp only [globalProduct]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (mul_nonneg (ht0 q) (abs_nonneg _))
        (one_div_nonneg.mpr (hpPos q).le)
  have hglobal : globalProduct ≤ 7 * w := by
    have htoL1 : globalProduct ≤ B.primeDeviationL1 := by
      dsimp only [globalProduct]
      unfold primeDeviationL1
      apply Finset.sum_le_sum
      intro q _hq
      have hfac : 0 ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) :=
        mul_nonneg (abs_nonneg _) (one_div_nonneg.mpr (hpPos q).le)
      calc
        tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
            (1 / (q.1 : ℝ)) =
          tPrime B.sampleData.n q.1 *
            (|B.primeDeviation q| * (1 / (q.1 : ℝ))) := by ring
        _ ≤ 1 * (|B.primeDeviation q| * (1 / (q.1 : ℝ))) :=
          mul_le_mul_of_nonneg_right (ht1 q) hfac
        _ = (1 / (q.1 : ℝ)) * |B.primeDeviation q| := by ring
    exact htoL1.trans hdevL1
  have hkernel : |kernel| ≤ (7 * CKernel * w) * alpha := by
    unfold kernel
    rw [abs_mul, abs_of_nonneg (one_div_nonneg.mpr hH.le)]
    calc
      (1 / H) *
          |∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) /
                    ((p.1 : ℝ) * (q.1 : ℝ))| ≤
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) /
                    ((p.1 : ℝ) * (q.1 : ℝ))| := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p _hp ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
              (CKernel * globalProduct) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        calc
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))|) ≤
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
                (CKernel *
                  (tPrime B.sampleData.n q.1 *
                    |B.primeDeviation q| *
                      (1 / (q.1 : ℝ)))) := by
            apply Finset.sum_le_sum
            intro q _hq
            rw [abs_div,
              abs_of_pos (mul_pos (hpPos p) (hpPos q)), abs_mul]
            calc
              (|B.primeDeviation q| *
                    |covarianceKernel
                      (tPrime B.sampleData.n p.1)
                      (tPrime B.sampleData.n q.1)|) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) ≤
                (|B.primeDeviation q| *
                    (CKernel * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1)) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_left
                  (hKernelProduct p q) (abs_nonneg _)
              _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
                  (CKernel *
                    (tPrime B.sampleData.n q.1 *
                      |B.primeDeviation q| *
                        (1 / (q.1 : ℝ)))) := by ring
          _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
              (CKernel * globalProduct) := by
            dsimp only [globalProduct]
            rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / H) *
          ((H * alpha) * (CKernel * (7 * w))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hfirstDiv :
            (∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = H * alpha := by
          calc
            _ = ∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
              apply Finset.sum_congr rfl
              intro p _hp
              ring
            _ = H * alpha := hfirstMoment
        rw [← Finset.sum_mul, hfirstDiv]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hglobal hCKernel)
          (mul_nonneg hH.le halpha.le)
      _ = (7 * CKernel * w) * alpha := by
        field_simp [hH.ne']
  rw [href]
  calc
    |diagonal + kernel| ≤ |diagonal| + |kernel| := abs_add_le _ _
    _ ≤ (CF * w) * alpha + (7 * CKernel * w) * alpha :=
      add_le_add hdiagonal hkernel
    _ = (CF + 7 * CKernel) * w * B.bandCenter i := by
      dsimp only [alpha]
      ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) {w CF CKernel : Real},
  LE.le.{0} (0 : Real) w →
    LE.le.{0} (0 : Real) CKernel →
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
                (1 : Real)))
            (HMul.hMul.{0, 0, 0} CF
              (Erdos390.Full.ArithmeticModel.tPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                ↑p))) →
        (∀
            (p q :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
            LE.le.{0}
              (abs.{0}
                (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    ↑p)
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    ↑q)))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} CKernel
                  (Erdos390.Full.ArithmeticModel.tPrime
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    ↑p))
                (Erdos390.Full.ArithmeticModel.tPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  ↑q))) →
          (∀
              (p :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)) w) →
            LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
                (HMul.hMul.{0, 0, 0} (7 : Real) w) →
              ∀ (i : Band),
                LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.referenceSlowRow.{u_1, u_2} B i))
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} CF (HMul.hMul.{0, 0, 0} (7 : Real) CKernel)) w)
                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceSlowRow_le_of_harmonicCentering
