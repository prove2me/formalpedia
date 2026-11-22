-- Prove2me | solution 1 for Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.momentReady_of_endpointMomentBounds
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:29:49.985114+00:00
-- url     : https://prove2.me/submissions/71c5a574-05d0-4c67-987b-f64f43df03d9

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
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic



























/-! ## The first logarithmic moment -/















/-! ## Quantitative PNT remainder -/





















/-! ## Exact alignment with the paper's logarithmic coordinate -/





/-- Rescaling both endpoints by `log z` leaves their harmonic-coordinate
length unchanged. -/
lemma log_logCoordinate_sub {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y) :
    Real.log (logCoordinate z Y) - Real.log (logCoordinate z A) =
      Real.log (Real.log (Y : ℝ)) -
        Real.log (Real.log (A : ℝ)) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hlogA0 : Real.log (A : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < A by omega)))
  have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
  unfold logCoordinate
  rw [Real.log_div hlogY0 hlogz0, Real.log_div hlogA0 hlogz0]
  ring

/-- The first continuum moment on a logarithmic cell is its ordinary
coordinate length. -/
lemma logCoordinate_sub {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) :
    logCoordinate z Y - logCoordinate z A =
      (Real.log (Y : ℝ) - Real.log (A : ℝ)) / Real.log z := by
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold logCoordinate
  field_simp [hlogz0]





















end Erdos390.Full.PrimeBandQuadrature

end

/- Source module: Erdos390.Full.PositiveCellTransfer -/
section


/-!
# Actual positive-cell prime-band transfer

This file connects the exact arithmetic band geometry to the unconditional
two-endpoint PNT quadrature.  A certificate records that each finite band is
literally a prime interval `(A_j,Y_j]` inside the actual moving prime band.
From that elementary membership statement we derive, rather than assume,

* `H_j = sum_{A_j < p <= Y_j} 1/p`, and
* `H_j * alpha_j = (sum_{A_j < p <= Y_j} log p / p) / log y`.

The final theorems then import the uniform constants and threshold from
`PrimeBandQuadrature`; no Mertens constant or moving-cell asymptotic appears
as a structure field.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PositiveCellTransfer

open ArithmeticModel PrimeSums PrimeBandQuadrature
open ArithmeticBandGeometry

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]







namespace IntervalCertificate

variable {P : Partition n W Band} (E : IntervalCertificate P)









omit [DecidableEq Band] in
lemma mem_cellPrimes_iff {j : Band} {p : ℕ} :
    p ∈ E.cellPrimes j ↔
      p.Prime ∧ E.lower j < p ∧ p ≤ E.upper j := by
  rw [cellPrimes, Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hzero, hpUpper⟩, hpPrime⟩, hpLower⟩
    refine ⟨hpPrime, ?_, hpUpper⟩
    by_contra hnot
    apply hpLower
    exact ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨⟨⟨Nat.zero_le p, hpUpper⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hzero, hpLower'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpLower') hpLower

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

omit [DecidableEq Band] in
lemma cellReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, 1 / (p : ℝ)) =
      fullReciprocalSum (E.upper j) - fullReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      1 / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j), 1 / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j), 1 / (p : ℝ)
  exact eq_sub_of_add_eq hsum

omit [DecidableEq Band] in
lemma cellLogReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, Real.log (p : ℝ) / (p : ℝ)) =
      fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      Real.log (p : ℝ) / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j),
      Real.log (p : ℝ) / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j),
        Real.log (p : ℝ) / (p : ℝ)
  exact eq_sub_of_add_eq hsum

lemma fiber_reciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, 1 / (q : ℝ) := by
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : ArithmeticBandGeometry.BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl

lemma fiber_logReciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j,
      Real.log (p.1 : ℝ) / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, Real.log (q : ℝ) / (q : ℝ) := by
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : ArithmeticBandGeometry.BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl

/-- Exact arithmetic identification of the harmonic cell mass. -/
theorem mass_eq_fullReciprocalSum_sub (j : Band) :
    P.mass j = fullReciprocalSum (E.upper j) -
      fullReciprocalSum (E.lower j) := by
  change (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = _
  rw [E.fiber_reciprocalSum_eq_cell, E.cellReciprocalSum_eq_sub]

private lemma mass_mul_center_eq_weightedCoordSum (j : Band) :
    P.mass j * P.center j =
      ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1 := by
  change P.data.mass j *
      ((∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
  field_simp [ne_of_gt (P.data.mass_pos j)]

/-- Exact arithmetic identification of the centered first cell moment. -/
theorem mass_mul_center_eq_fullLogReciprocalSum_sub (j : Band) :
    P.mass j * P.center j =
      (fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j)) / Real.log (y n) := by
  rw [mass_mul_center_eq_weightedCoordSum (P := P)]
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) *
        (Real.log (p.1 : ℝ) / Real.log (y n))) = _
  calc
    (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (Real.log (p.1 : ℝ) / Real.log (y n))) =
        (∑ p ∈ P.data.fiber j,
          Real.log (p.1 : ℝ) / (p.1 : ℝ)) /
            Real.log (y n) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro p hp
              ring
    _ = (∑ q ∈ E.cellPrimes j,
          Real.log (q : ℝ) / (q : ℝ)) /
            Real.log (y n) := by rw [E.fiber_logReciprocalSum_eq_cell]
    _ = _ := by rw [E.cellLogReciprocalSum_eq_sub]









end IntervalCertificate

end Erdos390.Full.PositiveCellTransfer

end

/- Source module: Erdos390.Full.PartitionPrimeDeviationGeometry -/
section


/-!
# Prime-deviation moments for an actual arithmetic partition

This is the sample-independent form of the arithmetic geometry in Lemma
8.6.  It works directly with `ArithmeticBandGeometry.Partition`, so the
regular mesh constructed from explicit natural endpoints can be audited
without first manufacturing the smooth-number probability space.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PositiveCellTransfer
open KernelPrimeQuadrature PrimeCoordinateSecondMoment

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : ArithmeticBandGeometry.Partition n W Band)

















/-- Reindex the actual square-coordinate moment from a certified band to its
natural prime interval. -/
theorem bandSecondMoment_eq_cellPrimeSum
    (E : IntervalCertificate P) (j : Band) :
    P.bandSecondMoment j =
      ∑ q ∈ E.cellPrimes j,
        squareCoordinate (realLogCoordinate (y n) (q : ℝ)) / (q : ℝ) := by
  unfold bandSecondMoment
  apply Finset.sum_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := mem_primeBand.mpr
      ⟨hqData.1, (E.cutoff_le_lower j).trans_lt hqData.2.1,
        hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    unfold squareCoordinate realLogCoordinate tPrime
    ring

theorem bandSecondMoment_eq_fullWeightedReciprocalSum_sub
    (E : IntervalCertificate P) (j : Band) :
    P.bandSecondMoment j =
      fullWeightedReciprocalSum squareCoordinate (y n) (E.upper j) -
        fullWeightedReciprocalSum squareCoordinate (y n) (E.lower j) := by
  rw [P.bandSecondMoment_eq_cellPrimeSum E j]
  have hsub : PrimeSums.primesUpTo (E.lower j) ⊆
      PrimeSums.primesUpTo (E.upper j) := by
    intro p hp
    simp only [PrimeSums.primesUpTo, Finset.mem_filter,
      Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (E.lower_le_upper j)⟩, hp.2⟩
  have hsum := Finset.sum_sdiff hsub
    (f := fun q : ℕ ↦
      squareCoordinate (realLogCoordinate (y n) (q : ℝ)) / (q : ℝ))
  change (∑ q ∈ PrimeSums.primesUpTo (E.upper j) \
      PrimeSums.primesUpTo (E.lower j),
        squareCoordinate (realLogCoordinate (y n) (q : ℝ)) / (q : ℝ)) = _
  exact eq_sub_of_add_eq hsum













end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBounds -/
section


/-!
# Actual arithmetic `L¹` and variance bounds for the regular mesh

The endpoints in this file are the explicit floored endpoints from
`RegularMeshPrimeCutoffs`, and every sum is over the actual primes.  The
first part proves the finite deterministic assembly.  The final part derives
its moment inputs from the proved PNT quadratures.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor

theorem y_gt_one {n : ℕ} (hn : 1 < n) : 1 < y n := by
  have hlog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  exact (Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le).mp hlog







namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)
  {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper















end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBoundsEventually -/
section


/-!
# Eventual actual-prime moment bounds on the canonical regular mesh

This file discharges the `MomentReady` inputs of
`RegularMeshActualMomentBounds` from the unconditional prime number theorem
quadratures.  The endpoint family is the canonical family of floored powers
of `y`; no continuum mesh, prime-population, or moment estimate is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)









































variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper

/-- Deterministic PNT assembly.  The three quadrature estimates are stated
with constants and thresholds selected before `n`, the partition, and its
endpoints. -/
theorem momentReady_of_endpointMomentBounds
    {Cmass Cfirst Csecond : ℝ} {Xmass Xfirst Xsecond : ℕ}
    (hW8 : 8 ≤ W)
    (hXmass : Xmass ≤ W) (hXfirst : Xfirst ≤ W)
    (hXsecond : Xsecond ≤ W)
    (hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3)
    (hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
        PrimeSums.fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2))
    (hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)))
    (B : EndpointMomentBounds M n W Cmass Cfirst Csecond) :
    MomentReady M P := by
  have hW2 : 2 ≤ W := hW8.trans' (by omega)
  have hy : 1 < y n := y_gt_one B.n_gt_one
  have hlogy : 0 < Real.log (y n) := Real.log_pos hy
  have hPositiveMass (k : Fin M.cellCount) :
      P.mass k.succ ≤ 3 * M.ratio := by
    have hAThreshold : Xmass ≤ E.lower k.succ :=
      hXmass.trans (E.cutoff_le_lower k.succ)
    have hQuad := hMass (E.lower k.succ) (E.upper k.succ)
      hAThreshold (E.lower_le_upper k.succ)
    have hA2 : 2 ≤ E.lower k.succ :=
      hW2.trans (E.cutoff_le_lower k.succ)
    have hMainEq :
        Real.log (Real.log (E.upper k.succ : ℝ)) -
            Real.log (Real.log (E.lower k.succ : ℝ)) =
          positiveContinuumMass M n W k := by
      rw [hLower k.succ, hUpper k.succ]
      have hCoord := log_logCoordinate_sub hy hA2
        (E.lower_le_upper k.succ)
      rw [hLower k.succ, hUpper k.succ] at hCoord
      symm
      exact hCoord
    have hMassError :
        |P.mass k.succ - positiveContinuumMass M n W k| ≤ M.ratio := by
      rw [E.mass_eq_fullReciprocalSum_sub, ← hMainEq]
      exact hQuad.trans (by
        rw [hLower k.succ]
        exact B.positiveMassError k)
    have hOneSide :
        P.mass k.succ - positiveContinuumMass M n W k ≤ M.ratio :=
      (le_abs_self _).trans hMassError
    linarith [B.positiveMain k]
  have hLowFirst : P.mass 0 * P.center 0 ≤ 2 * delta := by
    have hLowerZero : E.lower 0 = W := by
      simpa only [Fin.val_zero, fullCutoff_zero] using hLower 0
    have hAThreshold : Xfirst ≤ E.lower 0 := by
      rw [hLowerZero]
      exact hXfirst
    have hRaw := hFirst (E.lower 0) (E.upper 0) hAThreshold
      (E.lower_le_upper 0)
    have hRawW :
        |PrimeSums.fullLogReciprocalSum (E.upper 0) -
          PrimeSums.fullLogReciprocalSum (E.lower 0) -
          (Real.log (E.upper 0 : ℝ) -
            Real.log (E.lower 0 : ℝ))| ≤
          2 * Cfirst / Real.log (W : ℝ) ^ 3 +
            Cfirst / (2 * Real.log (W : ℝ) ^ 2) := by
      calc
        _ ≤ 2 * Cfirst / Real.log (E.lower 0 : ℝ) ^ 3 +
              Cfirst / (2 * Real.log (E.lower 0 : ℝ) ^ 2) := hRaw
        _ = _ := by rw [hLowerZero]
    have hNorm :
        |(PrimeSums.fullLogReciprocalSum (E.upper 0) -
              PrimeSums.fullLogReciprocalSum (E.lower 0)) /
              Real.log (y n) -
            (Real.log (E.upper 0 : ℝ) -
              Real.log (E.lower 0 : ℝ)) / Real.log (y n)| ≤
          (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
            Cfirst / (2 * Real.log (W : ℝ) ^ 2)) /
              Real.log (y n) := by
      rw [← sub_div, abs_div, abs_of_pos hlogy]
      exact div_le_div_of_nonneg_right hRawW hlogy.le
    have hMainEq :
        (Real.log (E.upper 0 : ℝ) -
            Real.log (E.lower 0 : ℝ)) / Real.log (y n) =
          lowFirstContinuum M n W := by
      rw [← logCoordinate_sub hy, hLower 0, hUpper 0]
      rfl
    have hActualError :
        |P.mass 0 * P.center 0 - lowFirstContinuum M n W| ≤
          delta / 2 := by
      rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub, ← hMainEq]
      exact hNorm.trans B.lowFirstError
    have hOneSide := (le_abs_self
      (P.mass 0 * P.center 0 - lowFirstContinuum M n W)).trans
        hActualError
    linarith [B.lowFirstMain]
  have hLowSecondError :
      |P.bandSecondMoment 0 - lowSecondContinuum M n W| ≤
        delta ^ 2 / 12 := by
    have hLowerZero : E.lower 0 = W := by
      simpa only [Fin.val_zero, fullCutoff_zero] using hLower 0
    have hAThreshold : Xsecond ≤ E.lower 0 := by
      rw [hLowerZero]
      exact hXsecond
    have hRaw := hSecond (y n) hy (E.lower 0) (E.upper 0)
      hAThreshold (E.lower_le_upper 0)
    rw [P.bandSecondMoment_eq_fullWeightedReciprocalSum_sub E]
    have hMainEq :
        (realLogCoordinate (y n) (E.upper 0 : ℝ) ^ 2 -
            realLogCoordinate (y n) (E.lower 0 : ℝ) ^ 2) / 2 =
          lowSecondContinuum M n W := by
      rw [hLower 0, hUpper 0]
      rfl
    rw [← hMainEq]
    exact hRaw.trans (by
      rw [hLowerZero]
      exact B.lowSecondError)
  have hLowSecondLower : delta ^ 2 / 3 ≤ P.bandSecondMoment 0 := by
    have hLowerSide := (neg_le_neg hLowSecondError).trans (neg_abs_le
      (P.bandSecondMoment 0 - lowSecondContinuum M n W))
    nlinarith [B.lowSecondMainLower]
  have hLowSecondUpper : P.bandSecondMoment 0 ≤ delta ^ 2 := by
    have hUpperSide := (le_abs_self
      (P.bandSecondMoment 0 - lowSecondContinuum M n W)).trans
        hLowSecondError
    nlinarith [B.lowSecondMainUpper]
  have hLowMass : 48 ≤ P.mass 0 := by
    have hLowerZero : E.lower 0 = W := by
      simpa only [Fin.val_zero, fullCutoff_zero] using hLower 0
    have hAThreshold : Xmass ≤ E.lower 0 := by
      rw [hLowerZero]
      exact hXmass
    have hRaw := hMass (E.lower 0) (E.upper 0) hAThreshold
      (E.lower_le_upper 0)
    have hMassError :
        |P.mass 0 -
          (Real.log (Real.log (E.upper 0 : ℝ)) -
            Real.log (Real.log (E.lower 0 : ℝ)))| ≤
          5 * Cmass / Real.log (W : ℝ) ^ 3 := by
      rw [E.mass_eq_fullReciprocalSum_sub]
      exact hRaw.trans_eq (by rw [hLowerZero])
    have hLowerSide := (neg_le_neg hMassError).trans (neg_abs_le
      (P.mass 0 - (Real.log (Real.log (E.upper 0 : ℝ)) -
        Real.log (Real.log (E.lower 0 : ℝ)))))
    have hUpperZero : E.upper 0 = fullCutoff M n W 1 := by
      simpa only [Fin.val_zero, Nat.zero_add] using hUpper 0
    have hMainBound :
        48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
          Real.log (Real.log (E.upper 0 : ℝ)) -
            Real.log (Real.log (E.lower 0 : ℝ)) := by
      rw [hLowerZero, hUpperZero]
      exact B.lowMassMain
    linarith
  exact ⟨hPositiveMass, hLowFirst, hLowSecondLower,
    hLowSecondUpper, hLowMass⟩









end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

theorem solution :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {n W : Nat}
  (P :
    Erdos390.Full.ArithmeticBandGeometry.Partition.{0} n W
      (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))))
  (E : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{0} P),
  (∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
      Eq.{1} (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{0} E j)
        (Erdos390.Full.RegularMeshPrimeCutoffs.fullCutoff M n W ↑j)) →
    (∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
        Eq.{1} (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{0} E j)
          (Erdos390.Full.RegularMeshPrimeCutoffs.fullCutoff M n W (HAdd.hAdd.{0, 0, 0} ↑j (1 : Nat)))) →
      ∀ {Cmass Cfirst Csecond : Real} {Xmass Xfirst Xsecond : Nat},
        LE.le.{0} (8 : Nat) W →
          LE.le.{0} Xmass W →
            LE.le.{0} Xfirst W →
              LE.le.{0} Xsecond W →
                (∀ (A Y : Nat),
                    LE.le.{0} Xmass A →
                      LE.le.{0} A Y →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimeSums.fullReciprocalSum Y)
                                (Erdos390.Full.PrimeSums.fullReciprocalSum A))
                              (HSub.hSub.{0, 0, 0} (Real.log (Real.log ↑Y)) (Real.log (Real.log ↑A)))))
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (5 : Real) Cmass)
                            (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat)))) →
                  (∀ (A Y : Nat),
                      LE.le.{0} Xfirst A →
                        LE.le.{0} A Y →
                          LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimeSums.fullLogReciprocalSum Y)
                                  (Erdos390.Full.PrimeSums.fullLogReciprocalSum A))
                                (HSub.hSub.{0, 0, 0} (Real.log ↑Y) (Real.log ↑A))))
                            (HAdd.hAdd.{0, 0, 0}
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) Cfirst)
                                (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat)))
                              (HDiv.hDiv.{0, 0, 0} Cfirst
                                (HMul.hMul.{0, 0, 0} (2 : Real) (HPow.hPow.{0, 0, 0} (Real.log ↑A) (2 : Nat)))))) →
                    (∀ (z : Real),
                        LT.lt.{0} (1 : Real) z →
                          ∀ (A Y : Nat),
                            LE.le.{0} Xsecond A →
                              LE.le.{0} A Y →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (HSub.hSub.{0, 0, 0}
                                        (Erdos390.Full.KernelPrimeQuadrature.fullWeightedReciprocalSum
                                          Erdos390.Full.PrimeCoordinateSecondMoment.squareCoordinate z Y)
                                        (Erdos390.Full.KernelPrimeQuadrature.fullWeightedReciprocalSum
                                          Erdos390.Full.PrimeCoordinateSecondMoment.squareCoordinate z A))
                                      (HDiv.hDiv.{0, 0, 0}
                                        (HSub.hSub.{0, 0, 0}
                                          (HPow.hPow.{0, 0, 0}
                                            (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑Y) (2 : Nat))
                                          (HPow.hPow.{0, 0, 0}
                                            (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑A) (2 : Nat)))
                                        (2 : Real))))
                                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) Csecond)
                                    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Real.log z) (2 : Nat)) (Real.log ↑A)))) →
                      Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.EndpointMomentBounds M n W Cmass Cfirst Csecond →
                        Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.MomentReady M P := by
  exact @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.momentReady_of_endpointMomentBounds
